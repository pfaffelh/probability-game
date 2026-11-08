// The stage of every world, in five screen sizes: a level's tip comes once, in a box that fits the
// screen; the page does not scroll (on a screen higher than 500 px) and is not wider than the screen;
// the tool bar and the status line are in view; Tips opens the tips again, Next goes to the next
// level (with its own tip), ← back.
// Usage: node tests/stage.mjs   (BASE=https://lean.mathematik.uni-freiburg.de/main/ for the server)
import { chromium } from 'playwright-core'
const base = (process.env.BASE ?? 'http://127.0.0.1:8004/main/').replace(/\/?$/, '/')
const sizes = [['large', 1920, 1080], ['laptop', 1366, 768], ['tablet', 768, 1024], ['phone', 390, 844], ['side', 844, 390]]
const browser = await chromium.launch({ executablePath: '/usr/bin/google-chrome', headless: true })
let failures = 0
const check = (ok, what) => { if (!ok) { failures++; console.log('FAIL', what) } }
for (const [name, width, height] of sizes) {
  const phone = width < 800
  const page = await (await browser.newContext({ viewport: { width, height }, isMobile: phone, hasTouch: phone })).newPage()
  page.on('pageerror', e => { failures++; console.log('PAGEERROR', e.message) })
  await page.goto(base)
  await page.evaluate(() => { localStorage.clear(); localStorage.setItem('pg:lang', 'de') })
  const pages = await page.evaluate(() => [...new Set([...document.querySelectorAll('a[href]')].map(a => /^([^/#?.]+)\/#/.exec(a.getAttribute('href'))?.[1]).filter(Boolean))])
  for (const path of pages) {
    const at = `${name} ${path}`
    await page.goto(base + path + '/'); await page.waitForTimeout(500)
    // the tip of the first level, once
    const box = page.locator('.pg-tip-card')
    check(await box.isVisible(), `${at}: no tip at the first level`)
    if (await box.isVisible()) {
      const b = await box.boundingBox()
      check(b.y >= 0 && b.y + b.height <= height + 1 && b.x >= 0 && b.x + b.width <= width + 1, `${at}: the tip is not in the screen`)
      check((await page.locator('.pg-tip-body').innerText()).length > 40, `${at}: the tip is empty`)
      await page.locator('.pg-tip-ok').click()
    }
    await page.reload(); await page.waitForTimeout(400)
    check(!(await box.isVisible()), `${at}: the tip again after a reload`)
    // the stage: nothing scrolls, the tool bar and the status in view
    const s = await page.evaluate(() => {
      const r = e => document.querySelector(e)?.getBoundingClientRect()
      return { sh: document.documentElement.scrollHeight, sw: document.documentElement.scrollWidth, bar: r('.pg-toolbar'), status: r('.pg-status'), text: document.querySelector('.pg-status')?.textContent ?? '', hash: location.hash }
    })
    if (height > 500) check(s.sh <= height + 1, `${at}: the page scrolls (${s.sh} > ${height})`)
    check(s.sw <= width + 1, `${at}: wider than the screen (${s.sw})`)
    check(s.bar && s.bar.bottom <= Math.max(height, s.sh) + 1 && s.bar.height > 0, `${at}: the tool bar is not in view`)
    if (height > 500) check(s.bar.bottom <= height + 1, `${at}: the tool bar is below the screen`)
    check(s.text.length > 0, `${at}: no status`)
    // Tips again, then closed with Escape
    await page.locator('.pg-toolbar .pg-tips-button').click()
    check(await box.isVisible(), `${at}: Tips opens nothing`)
    await page.keyboard.press('Escape')
    check(!(await box.isVisible()), `${at}: Escape does not close the tips`)
    // Next: the second level, with its tip; ← back
    await page.locator('.pg-toolbar .pg-next-button').click(); await page.waitForTimeout(300)
    check(await page.evaluate(() => location.hash) === '#level-2', `${at}: Next does not go to level 2`)
    check(await box.isVisible(), `${at}: no tip at level 2`)
    if (await box.isVisible()) await page.locator('.pg-tip-x').click()
    await page.keyboard.press('ArrowLeft'); await page.waitForTimeout(200)
    check(await page.evaluate(() => location.hash) === '#level-1', `${at}: ← does not go back`)
    console.log(`${at}: ${s.text}`)
  }
}
console.log('failures:', failures)
await browser.close()
process.exit(failures ? 1 : 0)
