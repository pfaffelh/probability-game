// Plays every level of the site in a browser, on a desktop and a phone: the board, then the proof,
// typed line by line. The worlds are those of the site's table of contents, in its order; the moves
// that solve a board (`play`) and the proof (`:::solution`) are those of the level in its source
// (tests/levels.py), matched by `data-world` and the order of the levels of this edition.
// In the edition `show` (boards alone) only the boards are played.
// Needs playwright-core and Chrome, the site and the bridge (see README):
//   node tests/play.mjs [desktop|phone]
//   ONLY=One-Coin node tests/play.mjs desktop     (one world)
//   BASE=https://lean.mathematik.uni-freiburg.de/main/ BACKEND= node tests/play.mjs   (the server)
import { chromium } from 'playwright-core'
import { execFileSync } from 'child_process'
const base = (process.env.BASE ?? 'http://127.0.0.1:8004/').replace(/\/?$/, '/')
const backend = process.env.BACKEND ?? 'http://127.0.0.1:8091'
const worlds = JSON.parse(execFileSync('python3', ['-I', new URL('levels.py', import.meta.url).pathname], { encoding: 'utf8' }))
const only = process.argv[2]  // 'desktop' or 'phone'
const browser = await chromium.launch({ executablePath: '/usr/bin/google-chrome', headless: true })
let fails = 0
const fail = what => { fails++; console.log('FAIL', what) }
for (const [name, vp] of [['desktop', { width: 1200, height: 900 }], ['phone', { width: 390, height: 844, isMobile: true, hasTouch: true }]]) {
  if (only && only !== name) continue
  const ctx = await browser.newContext({ viewport: { width: vp.width, height: vp.height }, isMobile: vp.isMobile, hasTouch: vp.hasTouch, deviceScaleFactor: 1 })
  const page = await ctx.newPage()
  page.on('pageerror', e => console.log('PAGEERROR', e.message))
  // the worlds of this edition, from the front page
  await page.goto(base)
  // (no tips popping up: tests/stage.mjs looks at them)
  await page.evaluate(b => { localStorage.clear(); localStorage.setItem('pg:lang', 'de'); localStorage.setItem('pg:tips', 'off'); if (b) localStorage.setItem('pg:backend', b) }, backend)
  await page.reload()
  const edition = await page.evaluate(() => document.querySelector('meta[name="pg-edition"]')?.content)
  const pages = await page.evaluate(() => [...new Set([...document.querySelectorAll('a[href]')].map(a => /^([^/#?.]+)\/#/.exec(a.getAttribute('href'))?.[1]).filter(Boolean))])
  const withProofs = edition !== 'show'
  console.log(`${name}: edition ${edition}, worlds ${pages.join(', ')}`)
  for (const path of pages) {
    if (process.env.ONLY && path !== process.env.ONLY) continue
    await page.goto(base + path + '/')
    const world = await page.evaluate(() => document.querySelector('.pg-level')?.dataset.world)
    if (!world && path === 'Lexicon') continue  // (no levels)
    if (!worlds[world]) { fail(`${path}: no levels of ${world} in the sources`); continue }
    const levels = worlds[world].filter(l => !l.edition || l.edition === (withProofs ? 'main' : 'show'))
    const lvl = () => page.locator('.pg-level:visible')
    const n = await page.locator('.pg-level').count()
    if (n !== levels.length) fail(`${path}: ${n} levels on the page, ${levels.length} in ${world}`)
    for (let i = 0; i < levels.length; i++) {
      const t0 = Date.now(), L = levels[i], moves = L.play.split(L.kind === 'build' ? ';' : ',').map(m => m.trim()).filter(Boolean)
      if (!moves.length) fail(`${path} level ${i + 1}: no (play := …) in its source`)
      const move = m => lvl().locator(`.pg-move[data-move="${m}"]`).first().click()
      if (L.kind === 'level') for (const m of moves) { await move(m); await page.waitForTimeout(1050) }
      else if (L.kind !== 'build') {
        for (const m of moves) { await move(m); await page.waitForTimeout(450) }
        if (withProofs) await lvl().locator('.pg-solved').waitFor({ timeout: 60000 }).catch(() => {})
      }
      else {
        // a step "M1 Z1 and": the lines by their names, then the function
        const line = name => lvl().locator('.pg-card', { has: page.locator('.pg-row-name', { hasText: new RegExp(`^${name}$`) }) })
        for (const step of moves) {
          const ws = step.split(/\s+/)
          for (const c of await lvl().locator('.pg-card-sel').all()) await c.click()
          for (const k of ws.slice(0, -1)) await line(k).click()
          await move(ws[ws.length - 1])
        }
        // check the newest line: chosen alone
        for (const c of await lvl().locator('.pg-card-sel').all()) await c.click()
        await lvl().locator('.pg-card').last().click()
        await lvl().locator('.pg-check').first().click()
      }
      await page.waitForTimeout(300)
      const board = await lvl().locator('.pg-solved').count()
      if (!withProofs || !L.proof) {
        // the boards alone: nothing of Lean on the page, and on to the next level
        const lean = await page.locator('.pg-level:visible .pg-lean, .pg-level:visible .pg-lean-state, .pg-level:visible .pg-proof, .pg-proof-text:visible').count()
        if (!board || (!withProofs && lean)) fail(`${name} ${path} level ${i + 1}: board ${board ? 'ok' : 'NOT'}, ${lean} parts of Lean shown`)
        else console.log(`${name} ${path.slice(0, 12)} level ${i + 1}: board ok (${Date.now() - t0} ms)`)
        if (i < levels.length - 1 && board) await lvl().locator('.pg-solved .pg-next').click()
        continue
      }
      await lvl().locator('.pg-solved .pg-next').click()
      // the proof
      const input = lvl().locator('.pg-proof-input input')
      await input.waitFor({ timeout: 60000 })
      const idle = async () => { await page.waitForFunction(() => !document.querySelector('.pg-level:not([hidden]) .pg-proof')?.textContent.includes('denkt'), null, { timeout: 120000 }) }
      await idle()
      let err = ''
      for (const line of L.solution) {
        await input.fill(line)
        await input.press('Enter')
        await page.waitForTimeout(50); await idle()
        err = await lvl().locator('.pg-proof-error').isVisible() ? await lvl().locator('.pg-proof-error').innerText() : ''
        if (err) { console.log(`   line "${line}": ${err.slice(0, 200)}`); break }
      }
      let proved = await lvl().locator('.pg-proof-done').count()
      // in the first level of each world: start the proof over (the lines go, the input comes back), and prove it again
      if (i === 0 && proved) {
        await page.locator('.pg-toolbar .pg-restart').click()
        await page.waitForTimeout(50); await idle()
        const fresh = !(await lvl().locator('.pg-proof-lines li').count()) && !(await lvl().locator('.pg-proof-done').count()) && await input.isVisible() && await lvl().locator('.pg-goal').count() > 0
        if (!fresh) fail(`${name} ${path}: start over is not back at the start`)
        for (const line of L.solution) { await input.fill(line); await input.press('Enter'); await page.waitForTimeout(50); await idle() }
        proved = await lvl().locator('.pg-proof-done').count()
        console.log(`   start over: ${fresh ? 'ok' : 'NOT'}, proved again: ${proved ? 'ok' : 'NOT'}`)
      }
      if (!board || !proved) fail(`${name} ${path} level ${i + 1}`)
      console.log(`${name} ${path.slice(0, 12)} level ${i + 1}: board ${board ? 'ok' : 'NOT'}, proof ${proved ? 'ok' : 'NOT'} (${L.solution.length} lines, ${Date.now() - t0} ms)`)
      if (i < levels.length - 1 && proved) await page.locator('.pg-toolbar .pg-next-button').click()
    }
    console.log(name, path.slice(0, 12), 'dots done:', await page.locator('.pg-dot-done').count(), 'half:', await page.locator('.pg-dot-half').count())
  }
}
console.log('failures:', fails)
await browser.close()
process.exit(fails ? 1 : 0)
