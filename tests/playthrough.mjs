// Plays the worlds as a player does, with the mouse, on the stage: for each level the board (gates
// from the side, wires from port to port, maps into fields, as in its `play`), then Next, the Lean
// proof line by line (its `:::solution`, typed and sent with Enter), and Next again. A level in Lean
// only is the proof alone. Reports, per level, whether the board turned green and the proof was done.
//   node tests/playthrough.mjs [World-path …]        (default: all worlds of the front page)
//   BASE=http://127.0.0.1:8004/main/ BACKEND=http://127.0.0.1:8091 PHONE=1
import { chromium } from 'playwright-core'
import { execFileSync } from 'child_process'
const base = (process.env.BASE ?? 'http://127.0.0.1:8004/main/').replace(/\/?$/, '/')
const backend = process.env.BACKEND ?? 'http://127.0.0.1:8091'
const sources = JSON.parse(execFileSync('python3', ['-I', new URL('levels.py', import.meta.url).pathname], { encoding: 'utf8' }))
const phone = !!process.env.PHONE
const browser = await chromium.launch({ executablePath: '/usr/bin/google-chrome', headless: true })
const ctx = await browser.newContext(phone ? { viewport: { width: 390, height: 844 }, isMobile: true, hasTouch: true } : { viewport: { width: 1300, height: 900 } })
const page = await ctx.newPage()
const errors = []
page.on('pageerror', e => errors.push(e.message))
let fails = 0
const fail = what => { fails++; console.log('  FAIL', what) }
await page.goto(base)
await page.evaluate(b => { localStorage.clear(); localStorage.setItem('pg:tips', 'off'); if (b) localStorage.setItem('pg:backend', b) }, backend)
await page.reload()
const edition = await page.evaluate(() => document.querySelector('meta[name="pg-edition"]')?.content)
const withProofs = edition !== 'show'
let paths = process.argv.slice(2)
if (!paths.length) paths = await page.evaluate(() => [...new Set([...document.querySelectorAll('a[href]')].map(a => /^([^/#?.]+)\/#/.exec(a.getAttribute('href'))?.[1]).filter(Boolean))].filter(p => p !== 'Lexicon'))
const L = '.pg-level:not([hidden]) '
const status = () => page.locator('.pg-status').first().innerText()
const ids = () => page.evaluate(() => [...document.querySelectorAll('.pg-level:not([hidden]) .pg-csvg .pg-cblock[data-id]')].map(g => g.dataset.id))
const idle = () => page.waitForFunction(() => !/thinking|denkt/.test(document.querySelector('.pg-status')?.textContent ?? ''), null, { timeout: 120000 }).catch(() => {})
const port = (id, kind, i = 0) => page.locator(`${L}.pg-cport[data-block="${id}"][data-kind="${kind}"][data-i="${i}"]`)

async function tapPalette(kind) {
  let item = page.locator(`${L}.pg-palette .pg-gate-item[data-move="${kind}"]`)
  if (!(await item.count()) || !(await item.first().isVisible())) {
    // a phone: the gates behind ＋
    await page.locator('.pg-stage-add, .pg-add-button, button:has-text("Gate")').first().click().catch(() => {})
    item = page.locator(`.pg-popover .pg-gate-item[data-move="${kind}"], .pg-pop .pg-gate-item[data-move="${kind}"]`)
  }
  await item.first().click()
  await page.waitForTimeout(120)
}

async function playCircuit(play) {
  const names = {}
  for (const st of play.split(';').map(s => s.trim()).filter(Boolean)) {
    let m
    if ((m = /^(\w+)=(\w+)$/.exec(st))) {
      const before = await ids(); await tapPalette(m[2])
      const after = await ids(); names[m[1]] = after.find(x => !before.includes(x)) ?? m[1]
    } else if ((m = /^(\w+)\.(\w+)=(\w+)$/.exec(st))) {
      await tapPalette('map:' + m[3])
    } else if ((m = /^(\w+)>(\w+)(?:\.(\d+))?$/.exec(st))) {
      await port(names[m[1]] ?? m[1], 'out').click({ force: true })
      await port(names[m[2]] ?? m[2], 'in', Number(m[3] ?? 0)).click({ force: true })
      await page.waitForTimeout(60)
    }
  }
  await page.waitForTimeout(300)
}

async function prove(lines) {
  const input = page.locator(`${L}.pg-proof-input input`)
  await input.waitFor({ timeout: 30000 }).catch(() => {})
  await idle()
  for (const line of lines) {
    await input.click(); await input.fill(line); await input.press('Enter')
    await page.waitForTimeout(80); await idle()
    const err = await page.locator(`${L}.pg-proof-error`).isVisible() ? await page.locator(`${L}.pg-proof-error`).innerText() : ''
    if (err) return `line "${line}": ${err.slice(0, 300)}`
  }
  return (await page.locator(`${L}.pg-proof-done`).count()) ? '' : 'not done after the last line'
}

for (const path of paths) {
  await page.goto(base + path + '/'); await page.waitForTimeout(800)
  const world = await page.evaluate(() => document.querySelector('.pg-level')?.dataset.world)
  const levels = (sources[world] ?? []).filter(l => !l.edition || l.edition === (withProofs ? 'main' : 'show')).filter(l => withProofs || l.kind !== 'leanonly')
  const n = await page.locator('.pg-level').count()
  console.log(`${path}: ${n} levels (${levels.length} in the source)`)
  if (n !== levels.length) fail(`${path}: ${n} levels on the page, ${levels.length} in the source`)
  for (let i = 0; i < levels.length; i++) {
    const lv = levels[i], t0 = Date.now()
    const shown = await page.evaluate(() => [...document.querySelectorAll('.pg-level')].findIndex(r => !r.hidden))
    if (shown !== i) fail(`${path} level ${i + 1}: level ${shown + 1} is shown`)
    let board = 'none', green = false
    if (lv.kind === 'circuit') {
      await playCircuit(lv.play)
      board = /goals accomplished/.test(await status()) ? 'ok' : `NOT (${await status()})`
      green = await page.locator(`${L}.pg-level-done, .pg-level-done:not([hidden])`).count() > 0
      if (board !== 'ok' || !green) fail(`${path} level ${i + 1}: board ${board}, green ${green}`)
    } else if (lv.kind !== 'leanonly') {
      fail(`${path} level ${i + 1}: kind ${lv.kind} not played by this script`)
    }
    let proof = 'none'
    if (withProofs && lv.proof) {
      if (lv.kind !== 'leanonly') { await page.locator('.pg-next-button').click(); await page.waitForTimeout(400) }
      const r = await prove(lv.solution)
      proof = r ? `NOT: ${r}` : 'ok'
      if (r) fail(`${path} level ${i + 1}: proof ${r}`)
    }
    console.log(`  ${i + 1} ${lv.kind}: board ${board}${green ? ' (green)' : ''}, proof ${proof} (${Date.now() - t0} ms)`)
    if (i < levels.length - 1) {
      // Next: to the next level (after a proof; or from a board without a proof)
      await page.locator('.pg-next-button').click(); await page.waitForTimeout(500)
    }
  }
}
if (errors.length) console.log('PAGE ERRORS:\n' + [...new Set(errors)].join('\n'))
console.log('failures:', fails)
await browser.close()
process.exit(fails || errors.length ? 1 : 0)
