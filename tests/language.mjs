// The language switch in the header, on every page: tapping DE shows German texts and headings (kept on
// reload), EN English again; one language at a time, nothing wider than a phone.
// The pages are the front page and the worlds of its table of contents.
// Usage: node tests/language.mjs   (BASE=https://lean.mathematik.uni-freiburg.de/main/ for the server)
import { chromium } from 'playwright-core'
const base = (process.env.BASE ?? 'http://127.0.0.1:8004/').replace(/\/?$/, '/')
const browser = await chromium.launch({ channel: 'chrome' })
const page = await (await browser.newContext({ viewport: { width: 390, height: 844 }, isMobile: true, hasTouch: true })).newPage()
page.on('pageerror', e => console.log('PAGEERROR', e.message))
let failures = 0
const check = (ok, what) => { if (!ok) { failures++; console.log('FAIL', what) } }
await page.goto(base); await page.evaluate(() => localStorage.clear()); await page.reload()
const pages = ['', ...await page.evaluate(() => [...new Set([...document.querySelectorAll('a[href]')].map(a => /^([^/#?.]+)\/#/.exec(a.getAttribute('href'))?.[1]).filter(Boolean))].map(p => p + '/'))]
for (const [lang, other, title] of [['de', 'en', 'Wahrscheinlichkeit|Wahr und falsch|Gitter|Münze|ziehen|Bauen|Zählen|Lexikon'], ['en', 'de', 'Probability|True and False|Grid|Coin|Draw|Building|Counting|Lexicon']]) {
  await page.locator('header .pg-langbtn', { hasText: lang.toUpperCase() }).click()
  await page.waitForLoadState('load'); await page.waitForTimeout(300)
  for (const path of pages) {
    await page.goto(base + path); await page.waitForTimeout(300)
    const s = await page.evaluate(other => ({
      lang: document.documentElement.lang, title: document.title, h1: document.querySelector('main h1')?.innerText ?? '',
      shown: document.querySelectorAll(`.pg-lang-${other}`).length - [...document.querySelectorAll(`.pg-lang-${other}`)].filter(e => !e.offsetParent).length,
      switch: !!document.querySelector('header .pg-langs'), wide: document.documentElement.scrollWidth > innerWidth,
      world: /(World|Welt) \d+: /.test(document.querySelector('main')?.innerText ?? ''),
    }), other)
    check(s.lang === lang, `${lang} ${path}: lang ${s.lang}`)
    check(new RegExp(title).test(s.title), `${lang} ${path}: title ${s.title}`)
    check(s.shown === 0, `${lang} ${path}: ${s.shown} blocks in ${other}`)
    check(s.switch, `${lang} ${path}: no switch in the header`)
    check(!s.wide, `${lang} ${path}: wider than the phone`)
    check(!s.world, `${lang} ${path}: "World n:" in the text`)
    console.log(`${lang} ${path || '/'}: ${s.title} | ${s.h1.replace(/­/g, '').replace(/\s+/g, ' ').slice(0, 40)}`)
  }
}
console.log('failures:', failures)
await browser.close()
process.exit(failures ? 1 : 0)
