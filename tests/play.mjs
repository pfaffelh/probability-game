// Plays every level in a browser: the board, then the proof, typed line by line (the solutions of
// Lean/SolutionsBool.lean, Lean/Solutions0.lean and Lean/Solutions.lean), on a desktop and a phone. Needs playwright-core and Chrome, the site on port
// 8004 and the bridge on 8091 (see README):  node tests/play.mjs [desktop|phone]
import { chromium } from 'playwright-core'
import { readFileSync } from 'fs'
const sol = ['SolutionsBool', 'Solutions0', 'Solutions'].map(f => readFileSync(new URL(`../Lean/${f}.lean`, import.meta.url), 'utf8')).join('\n')
const proofs = sol.split('\nexample ').slice(1).map(b => b.split(':= by\n')[1].split('\n').filter(l => l.startsWith('  ')).map(l => l.trim()))
const S = n => Array(n).fill('step')
const WB = [['not'], ['not', 'not'], ['immer false', 'not'], ['not', 'not'], ['not', 'not'], ['immer true', 'immer true'], ['not', 'not', 'not']]
const W0 = [['Norden'], ['Norden', 'Osten'], ['Osten', 'Norden'], ['Osten', 'step'], S(2), S(3), S(4), S(5)]
const W1 = [['not', 'not'], ['not'], ['immer true'], ['immer true', 'not'], ['toNat'], ['true: 5'], ['immer false', 'toNat'], ['not']]
const W2 = [
  ['c', 'c', [0, 1, 'und']], ['c', 'c', [1, 'nicht'], [0, 2, 'und']], ['c', 'c', [0, 1, 'oder']], ['c', [0, 'nicht'], [0, 1, 'und']],
  ['c', 'c', [0, 1, 'oder'], [0, 1, 'und'], [3, 'nicht'], [2, 4, 'und']], ['c', 'c', [0, 'toNat'], [1, 'toNat'], [2, 3, 'addieren']],
  ['c', 'c', 'c', [0, 1, 'und'], [0, 2, 'und'], [1, 2, 'und'], [3, 4, 5, 'oder']]]
const W3 = [['c', 'c', 'c', [0, 'toNat'], [1, 'toNat'], [2, 'toNat'], [3, 4, 5, 'addieren']], ['c', [0, 'toNat']],
  ['b', 'c', [1, 'toNat'], [0, 2, 'addieren']], ['b', [0, 'mindestens']], ['b', 'b', [0, 1, 'addieren']]]
const worlds = [['True-and-False', WB, 'walk'], ['World-0___-Walking-on-the-Grid', W0, 'walk'], ['World-1___-One-Coin', W1, 'level'], ['World-2___-Building-with-Coins', W2, 'build'], ['World-3___-Counting', W3, 'build']]
const only = process.argv[2]  // 'desktop' or 'phone'
const browser = await chromium.launch({ executablePath: '/usr/bin/google-chrome', headless: true })
let pi = 0, fails = 0
for (const [name, vp] of [['desktop', { width: 1200, height: 900 }], ['phone', { width: 390, height: 844, isMobile: true, hasTouch: true }]]) {
  if (only && only !== name) continue
  pi = 0
  const ctx = await browser.newContext({ viewport: { width: vp.width, height: vp.height }, isMobile: vp.isMobile, hasTouch: vp.hasTouch, deviceScaleFactor: 1 })
  const page = await ctx.newPage()
  page.on('pageerror', e => console.log('PAGEERROR', e.message))
  let first = true
  for (const [path, sols, kind] of worlds) {
    await page.goto(`http://127.0.0.1:8004/${path}/?backend=http://127.0.0.1:8091`)
    if (first) { await page.evaluate(() => { localStorage.clear(); localStorage.setItem('pg:lang', 'de'); localStorage.setItem('pg:backend', 'http://127.0.0.1:8091') }); await page.reload(); first = false }
    const lvl = () => page.locator('.pg-level:visible')
    for (let i = 0; i < sols.length; i++) {
      const t0 = Date.now()
      if (kind === 'level') for (const n of sols[i]) { await lvl().locator('.pg-move', { hasText: n }).first().click(); await page.waitForTimeout(1050) }
      else if (kind === 'walk') {
        for (const n of sols[i]) { await lvl().locator('.pg-move', { hasText: n }).first().click(); await page.waitForTimeout(450) }
        await lvl().locator('.pg-solved').waitFor({ timeout: 60000 }).catch(() => {})
      }
      else {
        for (const a of sols[i]) {
          if (a === 'c' || a === 'b') { await lvl().locator('.pg-coin-btn', { hasText: a === 'c' ? 'Münze' : 'B(2' }).click(); continue }
          for (const c of await lvl().locator('.pg-card-sel').all()) await c.click()
          for (const n of a.slice(0, -1)) await lvl().locator(`.pg-card[data-node="${n}"]`).click()
          await lvl().locator('.pg-move', { hasText: new RegExp(a[a.length - 1]) }).first().click()
        }
        await lvl().locator('.pg-check').first().click()
      }
      await page.waitForTimeout(300)
      const board = await lvl().locator('.pg-solved').count()
      await lvl().locator('.pg-solved .pg-next').click()
      // the proof
      const input = lvl().locator('.pg-proof-input input')
      await input.waitFor({ timeout: 60000 })
      const idle = async () => { await page.waitForFunction(() => !document.querySelector('.pg-level:not([hidden]) .pg-proof')?.textContent.includes('denkt'), null, { timeout: 120000 }) }
      await idle()
      let err = ''
      for (const line of proofs[pi]) {
        await input.fill(line)
        await input.press('Enter')
        await page.waitForTimeout(50); await idle()
        err = await lvl().locator('.pg-proof-error').isVisible() ? await lvl().locator('.pg-proof-error').innerText() : ''
        if (err) { console.log(`   line "${line}": ${err.slice(0, 200)}`); break }
      }
      let proved = await lvl().locator('.pg-proof-done').count()
      // in the first level of each world: start the proof over (the lines go, the input comes back), and prove it again
      if (i === 0 && proved) {
        await lvl().locator('.pg-proof .pg-tool', { hasText: 'Neu anfangen' }).click()
        await page.waitForTimeout(50); await idle()
        const fresh = !(await lvl().locator('.pg-proof-lines li').count()) && !(await lvl().locator('.pg-proof-done').count()) && await input.isVisible() && await lvl().locator('.pg-goal').count() > 0
        if (!fresh) { fails++; console.log(`   start over: not back at the start`) }
        for (const line of proofs[pi]) { await input.fill(line); await input.press('Enter'); await page.waitForTimeout(50); await idle() }
        proved = await lvl().locator('.pg-proof-done').count()
        console.log(`   start over: ${fresh ? 'ok' : 'NOT'}, proved again: ${proved ? 'ok' : 'NOT'}`)
      }
      if (!board || !proved) fails++
      console.log(`${name} ${path.slice(0, 7)} level ${i + 1}: board ${board ? 'ok' : 'NOT'}, proof ${proved ? 'ok' : 'NOT'} (${proofs[pi].length} lines, ${Date.now() - t0} ms)`)
      pi++
      if (i < sols.length - 1 && proved) await lvl().locator('.pg-proof .pg-next').click()
    }
    console.log(name, path.slice(0, 7), 'dots done:', await page.locator('.pg-dot-done').count(), 'half:', await page.locator('.pg-dot-half').count())
  }
}
console.log('failures:', fails)
await browser.close()
