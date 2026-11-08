// The probability game: distributions as bar charts, moves as maps, the result as the image measure.
//
// Each `.pg-level` (from `::::level` in ProbGame/Level.lean) has a start distribution, a target and
// the moves offered. A distribution is a space ('bool', 'nat', 'int') with masses on its points that
// are polynomials in p (with exact fractions: the same for every p); the picture draws them for an example p,
// which a slider changes; a move is a map, and applying it pushes the distribution forward: the mass of each
// point goes to its image (animated), where it adds up with the masses of the other points of the
// same image. A tapped bar shows its preimage. The level is solved when the distribution is the
// target; its Lean statement (for every p) is then shown. A world page shows one level at a time,
// with a dot per level above it; progress is kept in the browser.
(function () {
  'use strict'

  // ---------------------------------------------------------------- language

  // English, unless the player chose German with the switch EN | DE (not the browser's language).
  let LANG = 'en'
  try { LANG = localStorage.getItem('pg:lang') ?? 'en' } catch {}
  const DE = {
    Moves: 'Züge', Undo: 'Zurück', 'Start over': 'Neu anfangen', 'Next level ›': 'Nächstes Level ›',
    Target: 'Ziel', 'In Lean, for every p:': 'In Lean, für jedes p:', 'proved': 'bewiesen',
    'Tap a bar to see where its mass came from.': 'Tippe eine Säule an, um zu sehen, woher ihre Masse kommt.',
    'This move needs a coin, not a number.': 'Dieser Zug braucht eine Münze, keine Zahl.',
    'Level {i} of {n}': 'Level {i} von {n}', 'no mass comes here': 'hierher kommt keine Masse',
    '{b}: the mass comes from {from}, P = {sum}{m}': '{b}: Die Masse kommt aus {from}, P = {sum}{m}',
    'not: swap the sides': 'not: Seiten tauschen', 'always true': 'immer true', 'always false': 'immer false', 'do nothing': 'nichts tun',
    'toNat: false = 0, true = 1': 'toNat: false = 0, true = 1', 'true: win {a}, false: {b}': 'true: {a} gewinnen, false: {b}',
    'the start': 'der Anfang', 'Lean:': 'Lean:',
    'confirmed by Lean, for every p': 'von Lean bestätigt, für jedes p', 'Lean is normalising …': 'Lean normalisiert …',
    'Lean disagrees: the target is': 'Lean widerspricht: Das Ziel ist',
    'Lean is not connected: the board checks for every p by itself, without Lean.': 'Lean ist nicht verbunden: Das Spielfeld prüft selbst, für jedes p, aber ohne Lean.',
    'Task: bring the distribution into the shape of the target': 'Aufgabe: Bring die Verteilung in die Form des Ziels',
    'surely {b}': 'sicher {b}', 'the picture for p =': 'das Bild für p =', '(only an example; the masses hold for every p)': '(nur ein Beispiel; die Massen gelten für jedes p)',
  }
  // The edition of the site (`ProbGame.edition`, a meta tag in the head of every page, read in `init`,
  // when the head is there): `show` plays the boards alone, without Lean and without proofs; the
  // other editions have both.
  let SHOW = false
  // whether a part of a page (a level, …) belongs to this edition: not inside an `:::::only` of another
  const ours = e => { const o = e.closest('.pg-only'); return !o || o.dataset.edition === (SHOW ? 'show' : 'main') }
  const tr = (s, vars = {}) => (LANG === 'de' ? DE[s] ?? s : s).replace(/\{(\w+)\}/g, (_, k) => vars[k])
  const applyLang = () => {
    document.documentElement.classList.toggle('pg-de', LANG === 'de')
    document.documentElement.classList.toggle('pg-show', SHOW)
    document.documentElement.lang = LANG
  }
  // Headings of the site, which come from Verso.
  const DE_TITLES = {
    'The Probability Game': 'Das Wahrscheinlichkeits\u00ADspiel',  // (a soft hyphen, for phones)
    'One Coin': 'Eine Münze', 'Draw, then Compute': 'Erst ziehen, dann rechnen', 'Building with Coins': 'Bauen mit Münzen',
    'Counting': 'Zählen', 'Walking on the Grid': 'Gehen auf dem Gitter', 'True and False': 'Wahr und falsch', 'Lexicon': 'Lexikon', 'Table of Contents': 'Inhalt', 'Contents': 'Inhalt',
  }
  function translatePage() {
    const walk = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT)
    for (let n = walk.nextNode(); n; n = walk.nextNode()) {
      if (n.parentElement?.closest('.pg-level, .pg-lang')) continue
      if (LANG === 'de')
        for (const [en, de] of Object.entries(DE_TITLES)) if (n.nodeValue.includes(en)) n.nodeValue = n.nodeValue.replace(en, de)
      // The worlds are numbered anyway (1. …): "1. World 1: One Coin" is shown as "1. One Coin".
      n.nodeValue = n.nodeValue.replace(/(World|Welt) \d+: /g, '')
    }
    if (LANG === 'de') {
      for (const [en, de] of Object.entries(DE_TITLES)) document.title = document.title.replace(en, de.replace('\u00AD', ''))
      document.querySelectorAll('input[placeholder="Search..."]').forEach(i => { i.placeholder = 'Suchen …' })
    }
  }
  // The switch in the header: EN | DE. Changing the language reloads the page; progress is kept.
  function languageSwitch() {
    const header = document.querySelector('header')
    if (!header || header.querySelector('.pg-langs')) return
    const box = el('div', 'pg-langs')
    for (const l of ['en', 'de']) {
      const b = el('button', 'pg-langbtn' + (LANG === l ? ' pg-current' : ''), l.toUpperCase())
      b.type = 'button'
      b.setAttribute('aria-pressed', l === LANG)
      b.addEventListener('click', () => {
        if (l === LANG) return
        try { localStorage.setItem('pg:lang', l) } catch {}
        location.reload()
      })
      box.append(b)
    }
    header.append(box)
  }

  const el = (tag, cls, text) => {
    const e = document.createElement(tag)
    if (cls) e.className = cls
    if (text !== undefined) e.textContent = text
    return e
  }
  const svg = (tag, attrs = {}, text) => {
    const e = document.createElementNS('http://www.w3.org/2000/svg', tag)
    for (const [k, v] of Object.entries(attrs)) e.setAttribute(k, v)
    if (text !== undefined) e.textContent = text
    return e
  }

  // ---------------------------------------------------------------- Lean

  // A backend with Lean (server/bridge.py, with the journal's DiscreteMeasure as base): on a server,
  // `/lean` next to the site; else `?backend=http://127.0.0.1:8091` in the address (kept;
  // `?backend=` switches it off). After each move it normalises the state with the rules of the
  // world; a level is solved when the state and the target have the same normal form, for every p.
  let BACKEND = (() => {
    const local = !/^https?:$/.test(location.protocol) || /^(localhost|127\.0\.0\.1|\[::1\])$/.test(location.hostname)
    const served = local ? null : location.origin + '/lean'
    try {
      const q = new URLSearchParams(location.search).get('backend')
      if (q !== null) { if (q) localStorage.setItem('pg:backend', q); else localStorage.setItem('pg:backend', '') }
      const stored = localStorage.getItem('pg:backend')
      return stored === null ? served : stored || null
    } catch { return served }
  })()
  const RULES = "coin_not', unitInterval.symm_symm, ProbGame.coin_map_const, ProbGame.map_fun_id, map_pure, Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false"
  // a term of DiscreteMeasure as the proofs write it: `map f μ` and `μ.map f` as `f <$> μ`
  const functorForm = t => {
    t = t.trim().replace(/DiscreteMeasure\.pure/g, 'pure')
    // the next argument: a bracket, or a word
    const arg = s => {
      s = s.trimStart()
      if (s[0] !== '(') { const m = /^\S+/.exec(s)[0]; return [m, s.slice(m.length)] }
      let d = 0
      for (let i = 0; i < s.length; i++) { d += s[i] === '(' ? 1 : s[i] === ')' ? -1 : 0; if (!d) return [s.slice(0, i + 1), s.slice(i + 1)] }
      return [s, '']
    }
    const unbracket = s => (s[0] === '(' && arg(s)[1].trim() === '' ? s.slice(1, -1) : s)
    if (t.startsWith('map ')) {
      const [f, rest] = arg(t.slice(4)), [mu] = arg(rest), inner = functorForm(unbracket(mu))
      return `${f} <$> ${inner.includes('<$>') ? `(${inner})` : inner}`
    }
    // (μ).map f, as the moves are written
    const m = /^\((.*)\)\.map (.*)$/.exec(t)
    if (m) { const inner = functorForm(m[1]); return `${m[2]} <$> ${inner.includes('<$>') ? `(${inner})` : inner}` }
    return t
  }
  const normalForms = new Map()
  // the normal form of a Lean expression (a promise of { result } or { error })
  const normalise = (context, expr, how = { open: 'MeasureTheory DiscreteMeasure unitInterval', vars: '(p : unitInterval)', rules: RULES }) => {
    if (!BACKEND) return Promise.resolve({ error: { message: 'no backend' } })
    if (!normalForms.has(expr))
      normalForms.set(expr, fetch(BACKEND.replace(/\/$/, '') + '/simp', { method: 'POST', headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ context, ...how, expr }) })
        .then(r => r.json()).catch(e => ({ error: { message: String(e) } })))
    return normalForms.get(expr)
  }

  // ---------------------------------------------------------------- exact fractions

  const gcd = (a, b) => (b ? gcd(b, a % b) : Math.abs(a))
  class Q {
    constructor(n, d = 1) {
      if (d < 0) { n = -n; d = -d }
      const g = gcd(n, d) || 1
      this.n = n / g; this.d = d / g
    }
    add(o) { return new Q(this.n * o.d + o.n * this.d, this.d * o.d) }
    eq(o) { return this.n === o.n && this.d === o.d }
    get zero() { return this.n === 0 }
    get value() { return this.n / this.d }
    toString() { return this.d === 1 ? String(this.n) : `${this.n}/${this.d}` }
  }
  const parseQ = s => { const [n, d] = s.split('/'); return new Q(Number(n), Number(d ?? 1)) }
  const neg = q => new Q(-q.n, q.d)

  // A mass: a polynomial in p with exact fractions as coefficients (c[i] at p^i), the same for every
  // p; two masses are equal for every p exactly when their coefficients are.
  class Poly {
    constructor(c) {
      c = c.slice(); while (c.length && c[c.length - 1].zero) c.pop()
      this.c = c
    }
    coef(i) { return this.c[i] ?? new Q(0) }
    add(o) { return new Poly(Array.from({ length: Math.max(this.c.length, o.c.length) }, (_, i) => this.coef(i).add(o.coef(i)))) }
    neg() { return new Poly(this.c.map(neg)) }
    sub(o) { return this.add(o.neg()) }
    mul(o) {
      const r = Array.from({ length: Math.max(0, this.c.length + o.c.length - 1) }, () => new Q(0))
      this.c.forEach((a, i) => o.c.forEach((b, j) => { r[i + j] = r[i + j].add(new Q(a.n * b.n, a.d * b.d)) }))
      return new Poly(r)
    }
    eq(o) { return this.sub(o).zero }
    get zero() { return this.c.length === 0 }
    value(p) { return this.c.reduce((s, q, i) => s + q.value * p ** i, 0) }
    toString() { return this.text ?? showPoly(this) }
  }
  const SUP = n => (n === 1 ? '' : String(n).replace(/\d/g, d => '⁰¹²³⁴⁵⁶⁷⁸⁹'[d]))
  const showQ = q => String(q).replace('-', '−')
  // c·p^i·(1 − p)^j, when the mass is of this form (as in the binomial masses); else as a sum
  function showPoly(m) {
    if (m.zero) return '0'
    if (m.c.length === 1) return showQ(m.c[0])
    let i = 0; while (m.c[i].zero) i++
    let r = new Poly(m.c.slice(i)), j = 0
    // divide by 1 − p while 1 is a root
    while (r.c.length > 1 && r.c.reduce((s, q) => s.add(q), new Q(0)).zero) {
      const d = r.c.length - 1, b = Array(d)
      b[d - 1] = r.c[d]
      for (let k = d - 1; k >= 1; k--) b[k - 1] = r.c[k].add(b[k])
      r = new Poly(b).neg(); j++
    }
    if (j > 0 && r.c.length === 1) {
      const c = r.c[0], cs = c.n === c.d ? '' : c.n === -c.d ? '−' : showQ(c)
      return `${cs}${i ? 'p' + SUP(i) : ''}${j === 1 && !i && !cs ? '1 − p' : `(1 − p)${SUP(j)}`}`
    }
    let out = ''
    m.c.forEach((q, k) => {
      if (q.zero) return
      const a = new Q(Math.abs(q.n), q.d), sign = q.n < 0 ? '−' : '+'
      const body = k === 0 ? String(a) : `${a.n === a.d ? '' : a.d === 1 ? String(a) : a + '·'}p${SUP(k)}`
      out += out ? ` ${sign} ${body}` : (sign === '−' ? '−' : '') + body
    })
    return out
  }
  // a mass as a term of a sum: in brackets when it is a sum itself
  const paren = m => (/ [+−] /.test(m.toString().replace(/\([^)]*\)/g, '')) ? `(${m})` : m.toString())
  // `p`, `1-p`, `p^2`, `2p(1-p)`, `(1-p)^2`, `1/2`, `3p^2-2p^3`; shown as written
  function parsePoly(str) {
    const r = parsePoly1(str)
    r.text = str.replace(/\s/g, '').replace(/\^(\d+)/g, (_, n) => SUP(Number(n))).replace(/\*/g, '·')
      .replace(/(?<=[\dp)²³⁴⁵⁶⁷⁸⁹])-/g, ' − ').replace(/\+/g, ' + ').replace(/-/g, '−')
    return r
  }
  function parsePoly1(str) {
    const t = str.replace(/\s/g, '').match(/\d+|[p+\-*/^()]/g) ?? []
    let i = 0
    const peek = () => t[i], take = () => t[i++]
    const expr = () => {
      let r = term()
      while (peek() === '+' || peek() === '-') r = take() === '+' ? r.add(term()) : r.sub(term())
      return r
    }
    const term = () => {
      let r = factor()
      for (;;) {
        if (peek() === '*') { take(); r = r.mul(factor()) }
        else if (peek() === '/') { take(); const d = factor(); r = r.mul(new Poly([new Q(d.c[0].d, d.c[0].n)])) }
        else if (peek() !== undefined && /^(\d+|p|\()$/.test(peek())) r = r.mul(factor())
        else return r
      }
    }
    const factor = () => {
      if (peek() === '-') { take(); return factor().neg() }
      let b
      const x = take()
      if (x === 'p') b = new Poly([new Q(0), new Q(1)])
      else if (x === '(') { b = expr(); take() }
      else b = new Poly([new Q(Number(x))])
      if (peek() === '^') { take(); const n = Number(take()); let r = ONE; for (let k = 0; k < n; k++) r = r.mul(b); b = r }
      return b
    }
    return expr()
  }
  const ONE = new Poly([new Q(1)]), ZERO = new Poly([]), PP = new Poly([new Q(0), new Q(1)])
  const complement = m => ONE.sub(m)
  // the example p of the picture
  let P = 0.3
  try { P = Number(localStorage.getItem('pg:p') ?? 0.3) || 0.3 } catch {}

  // ---------------------------------------------------------------- distributions

  // A distribution: a space and the masses of its points (keys: 'true'/'false', or numbers as text).
  function parseDist(spec) {
    const w = spec.trim().split(/\s+/)
    if (w[0] === 'bernoulli') { const m = parsePoly(w[1]); return { space: 'bool', mass: new Map([['true', m], ['false', complement(m)]]) } }
    if (w[0] === 'pure') return { space: /^-?\d+$/.test(w[1]) ? 'nat' : 'bool', mass: new Map([[w[1], ONE]]) }
    return { space: w[0], mass: new Map(w.slice(1).map(x => { const [k, q] = x.split(':'); return [k, parsePoly(q)] })) }
  }
  const sameDist = (a, b) => {
    if (a.space !== b.space) return false
    const keys = new Set([...a.mass.keys(), ...b.mass.keys()])
    return [...keys].every(k => (a.mass.get(k) ?? ZERO).eq(b.mass.get(k) ?? ZERO))
  }
  // the points shown on the axis: a coin always shows both sides, false left and true right (as 0
  // and 1 on the numbers, so that renaming moves nothing sideways); numbers in their order
  const axis = (space, keys) => space === 'bool' ? ['false', 'true']
    : [...new Set(keys)].sort((x, y) => Number(x) - Number(y))
  const pointName = (space, k) => k
  const spaceName = s => ({ bool: 'Bool', nat: 'ℕ', int: 'ℤ' })[s]

  // ---------------------------------------------------------------- moves

  // A move: a map from one space to another, with its name and its Lean form.
  function parseMove(spec) {
    const w = spec.trim().split(/\s+/)
    switch (w[0]) {
      case 'id': return { from: 'bool', to: 'bool', f: k => k, lean: '(fun x => x)', label: () => tr('do nothing') }
      case 'not': return { from: 'bool', to: 'bool', f: k => (k === 'true' ? 'false' : 'true'), lean: 'not', label: () => tr('not: swap the sides') }
      case 'heads': return { from: 'bool', to: 'bool', f: () => 'true', lean: '(fun _ => true)', label: () => tr('always true') }
      case 'tails': return { from: 'bool', to: 'bool', f: () => 'false', lean: '(fun _ => false)', label: () => tr('always false') }
      case 'toNat': return { from: 'bool', to: 'nat', f: k => (k === 'true' ? '1' : '0'), lean: 'Bool.toNat', label: () => tr('toNat: false = 0, true = 1') }
      case 'payoff': {
        const [a, b] = [w[1], w[2]]
        return { from: 'bool', to: 'int', f: k => (k === 'true' ? a : b), lean: `(fun b => if b then (${a} : ℤ) else ${b})`,
          label: () => tr('true: win {a}, false: {b}', { a, b }) }
      }
    }
    throw new Error(`unknown move ${spec}`)
  }
  // the image measure: the mass of each point goes to its image
  const push = (dist, move) => {
    const mass = new Map()
    for (const [k, m] of dist.mass) { const b = move.f(k); mass.set(b, (mass.get(b) ?? ZERO).add(m)) }
    return { space: move.to, mass }
  }

  // ---------------------------------------------------------------- one level

  const W = 560, H = 210, BASE = 250, BAR = 74
  const layout = (keys) => {
    const gap = Math.min(150, (W - 40) / Math.max(1, keys.length))
    const x0 = W / 2 - (gap * (keys.length - 1)) / 2
    return Object.fromEntries(keys.map((k, i) => [k, x0 + i * gap]))
  }

  class Level {
    constructor(root, index, onSolved) {
      this.root = root; this.index = index; this.onSolved = onSolved
      this.start = parseDist(root.dataset.start)
      this.target = parseDist(root.dataset.target)
      this.moves = root.dataset.moves.split(',').map(parseMove)
      this.count = Number(root.dataset.count || 0)  // the number of moves, when it is prescribed
      this.leanStatement = root.dataset.lean
      this.startSpec = root.dataset.start
      this.steps = []  // the moves played: { move, before }
      this.dist = this.start
      this.picked = null
      this.board = root.querySelector('.pg-board')
      this.key = `pg:${location.pathname}:${index}`
      this.context = root.dataset.context ?? ''
      this.leanStart = root.dataset.leanStart || 'coin p'
      this.leanTarget = root.dataset.leanTarget
      this.leanNow = null; this.leanGoal = null
      if (this.leanTarget) normalise(this.context, this.leanTarget).then(r => { this.leanGoal = r; this.render() })
      this.updateLean()
      this.render()
    }

    get solved() { try { return localStorage.getItem(this.key) === '1' } catch { return false } }

    // the keys on the axis now (and the target's, when it lives on the same space)
    keys(dist = this.dist) {
      const ks = [...dist.mass.keys()]
      if (dist.space === this.target.space) ks.push(...this.target.mass.keys())
      return axis(dist.space, ks)
    }

    // the moves played, as a DiscreteMeasure, normalised by Lean
    leanState() {
      let e = this.leanStart
      for (const s of this.steps) e = `(${e}).map ${s.move.lean}`
      return e
    }
    updateLean() {
      const expr = this.leanState()
      this.leanNow = null
      normalise(this.context, expr).then(r => { if (this.leanState() === expr) { this.leanNow = r; this.render(); this.check() } })
    }
    // whether Lean agrees: null while it is asked or not connected
    leanAgrees() {
      if (!BACKEND || !this.leanTarget || !this.leanNow?.result || !this.leanGoal?.result) return null
      return this.leanNow.result === this.leanGoal.result
    }

    play(move) {
      if (this.animating) return
      if (move.from !== this.dist.space) { this.flash(tr('This move needs a coin, not a number.')); return }
      const before = this.dist, after = push(before, move)
      this.steps.push({ move, before })
      this.picked = null
      this.updateLean()
      this.animate(before, after, move, () => { this.dist = after; this.render(); this.check() })
    }
    undo() { if (this.animating || !this.steps.length) return; this.dist = this.steps.pop().before; this.picked = null; this.updateLean(); this.render() }
    reset() { if (this.animating) return; this.steps = []; this.dist = this.start; this.picked = null; this.updateLean(); this.render() }
    get canUndo() { return this.steps.length > 0 }
    // what to do next, in a line below the board
    status() {
      if (this.done) return 'goals accomplished 🎉'
      if (!this.steps.length) return tr('Tap a move.')
      if (this.count && this.steps.length > this.count) return tr('Too many moves: undo, or start over.')
      const d = this.dist, t = this.target
      if (d.space !== t.space) return tr('The distribution lives on {a}, the target on {b}.', { a: spaceName(d.space), b: spaceName(t.space) })
      if (sameDist(d, t)) {
        if (this.count && this.steps.length !== this.count) return tr('The right shape, but in {n} moves, please.', { n: this.count })
        return this.leanAgrees() === false ? tr('Lean disagrees.') : tr('Lean is checking …')
      }
      const k = axis(t.space, [...d.mass.keys(), ...t.mass.keys()]).find(k => !(d.mass.get(k) ?? ZERO).eq(t.mass.get(k) ?? ZERO))
      return tr('At {k}: P = {m}, the target has {t}.', { k: pointName(t.space, k), m: String(d.mass.get(k) ?? ZERO), t: String(t.mass.get(k) ?? ZERO) })
    }

    // solved: the distribution is the target, and Lean agrees (if it is connected)
    get done() { return this.steps.length > 0 && (!this.count || this.steps.length === this.count) && sameDist(this.dist, this.target) && this.leanAgrees() !== false && (!BACKEND || !this.leanTarget || this.leanAgrees() === true) }

    check() {
      if (this.animating || !this.done) return
      const first = !this.solved
      try { localStorage.setItem(this.key, '1') } catch {}
      this.render()
      this.onSolved?.(first)
    }

    flash(text) { this.info.textContent = text; this.info.classList.add('pg-warn'); setTimeout(() => this.info.classList.remove('pg-warn'), 1200) }

    // The mass of each point goes to its image, adding up there (900 ms).
    animate(before, after, move, done) {
      const ka = this.keys(before), kb = this.keys(after), xa = layout(ka), xb = layout(kb)
      const g = svg('g', { class: 'pg-flow' })
      this.svg.querySelectorAll('.pg-bar, .pg-mass, .pg-target').forEach(e => e.classList.add('pg-fading'))
      const stack = {}, parts = []
      for (const k of ka) {
        const m = before.mass.get(k)
        if (!m || m.zero) continue
        const b = move.f(k), h = m.value(P) * H
        const y0 = BASE - h, y1 = BASE - (stack[b] ?? 0) - h
        stack[b] = (stack[b] ?? 0) + h
        const r = svg('rect', { class: 'pg-mass', x: xa[k] - BAR / 2, y: y0, width: BAR, height: h, rx: 3 })
        const a = svg('line', { class: 'pg-arrow', x1: xa[k], y1: BASE + 8, x2: xb[b], y2: BASE + 8, 'marker-end': 'url(#pg-head)' })
        g.append(a, r)
        parts.push({ r, x0: xa[k], x1: xb[b], y0, y1 })
      }
      this.svg.append(g)
      this.animating = true
      const t0 = performance.now(), T = matchMedia?.('(prefers-reduced-motion: reduce)').matches ? 1 : 900
      const ease = t => (t < 0.5 ? 2 * t * t : 1 - (-2 * t + 2) ** 2 / 2)
      const step = now => {
        const t = Math.min(1, (now - t0) / T), e = ease(t)
        for (const p of parts) { p.r.setAttribute('x', p.x0 + (p.x1 - p.x0) * e - BAR / 2); p.r.setAttribute('y', p.y0 + (p.y1 - p.y0) * e) }
        if (t < 1) requestAnimationFrame(step)
        else { this.animating = false; done() }
      }
      requestAnimationFrame(step)
    }

    // the target, small, beside the board
    targetPicture() {
      const t = this.target, ks = axis(t.space, [...t.mass.keys()])
      const gap = Math.max(46, ...ks.map(k => String(t.mass.get(k) ?? ZERO).length * 7 + 8)), w = Math.max(200, gap * ks.length + 16), h = 150, base = 120, bh = 95, x0 = w / 2 - (gap * (ks.length - 1)) / 2, bw = Math.min(40, gap - 10)
      const g = svg('svg', { viewBox: `0 0 ${w} ${h}`, class: 'pg-target-svg', width: w })
      g.append(svg('text', { x: 6, y: 16, class: 'pg-target-title' }, tr('Target')))
      g.append(svg('line', { x1: 6, x2: w - 6, y1: base, y2: base, class: 'pg-axis' }))
      ks.forEach((k, i) => {
        const m = t.mass.get(k) ?? ZERO, x = x0 + i * gap, hh = m.value(P) * bh
        if (hh > 0) g.append(svg('rect', { class: 'pg-target-mass', x: x - bw / 2, y: base - hh, width: bw, height: hh, rx: 3 }))
        g.append(svg('text', { x, y: base - hh - 5, 'text-anchor': 'middle', class: 'pg-target-mass' }, m.toString()))
        g.append(svg('text', { x, y: base + 16, 'text-anchor': 'middle', class: 'pg-target-point' }, pointName(t.space, k)))
      })
      g.append(svg('text', { x: w - 8, y: 16, 'text-anchor': 'end', class: 'pg-space' }, spaceName(t.space)))
      return g
    }

    render() {
      const d = this.dist, keys = this.keys(), xs = layout(keys)
      const done = this.done
      const s = svg('svg', { viewBox: `0 0 ${W} 300`, class: 'pg-svg' + (done ? ' pg-done' : '') })
      const defs = svg('defs')
      const mk = svg('marker', { id: 'pg-head', viewBox: '0 0 10 10', refX: 9, refY: 5, markerWidth: 7, markerHeight: 7, orient: 'auto-start-reverse' })
      mk.append(svg('path', { d: 'M0,0 L10,5 L0,10 z', class: 'pg-arrowhead' }))
      defs.append(mk); s.append(defs)
      s.append(svg('line', { x1: 10, x2: W - 10, y1: BASE, y2: BASE, class: 'pg-axis' }))
      s.append(svg('text', { x: W - 12, y: BASE + 42, 'text-anchor': 'end', class: 'pg-space' }, spaceName(d.space)))
      // the target, dashed, where it lives on the same space
      if (d.space === this.target.space)
        for (const k of keys) {
          const m = this.target.mass.get(k)
          if (!m || m.zero) continue
          s.append(svg('rect', { class: 'pg-target', x: xs[k] - BAR / 2 - 6, y: BASE - m.value(P) * H - 6, width: BAR + 12, height: m.value(P) * H + 6, rx: 6 }))
        }
      for (const k of keys) {
        const m = d.mass.get(k) ?? ZERO, h = m.value(P) * H
        const bar = svg('g', { class: 'pg-bar' + (this.picked === k ? ' pg-picked' : '') })
        bar.append(svg('rect', { class: 'pg-hit', x: xs[k] - BAR / 2 - 8, y: 20, width: BAR + 16, height: BASE - 20 }))
        if (h > 0) bar.append(svg('rect', { class: 'pg-mass', x: xs[k] - BAR / 2, y: BASE - h, width: BAR, height: h, rx: 3 }))
        bar.append(svg('text', { x: xs[k], y: BASE - h - 8, 'text-anchor': 'middle', class: 'pg-mass' }, m.toString()))
        bar.append(svg('text', { x: xs[k], y: BASE + 24, 'text-anchor': 'middle', class: 'pg-point' }, pointName(d.space, k)))
        bar.addEventListener('click', () => { this.picked = this.picked === k ? null : k; this.render() })
        s.append(bar)
      }
      this.svg = s

      const moves = el('div', 'pg-moves')
      for (const m of this.moves) {
        const b = el('button', 'pg-move' + (m.from === d.space ? '' : ' pg-move-off'), m.label())
        b.type = 'button'
        b.title = `map ${m.lean}`
        b.addEventListener('click', () => this.play(m))
        moves.append(b)
      }
      const tools = el('div', 'pg-tools')
      const undo = el('button', 'pg-tool', '↶ ' + tr('Undo')), reset = el('button', 'pg-tool', '⟲ ' + tr('Start over'))
      undo.type = reset.type = 'button'
      undo.disabled = reset.disabled = !this.steps.length
      undo.addEventListener('click', () => this.undo()); reset.addEventListener('click', () => this.reset())
      tools.append(undo, reset)

      // what a tapped bar is made of: its preimage under the last move
      this.info = el('div', 'pg-info')
      if (this.picked !== null) {
        const m = d.mass.get(this.picked) ?? ZERO, name = pointName(d.space, this.picked)
        const last = this.steps[this.steps.length - 1]
        if (last) {
          const pre = axis(last.before.space, [...last.before.mass.keys()]).filter(k => last.before.mass.has(k) && last.move.f(k) === this.picked)
          const from = `{${pre.map(k => pointName(last.before.space, k)).join(', ')}}`
          const sum = pre.length > 1 ? `${pre.map(k => { const q = last.before.mass.get(k); return paren(q) }).join(' + ')} = ` : ''
          this.info.textContent = pre.length ? tr('{b}: the mass comes from {from}, P = {sum}{m}', { b: name, from, sum, m: m.toString() })
            : `${name}: ${tr('no mass comes here')}`
        } else this.info.textContent = `${name}: P = ${m} (${tr('the start')})`
      } else this.info.textContent = tr('Tap a bar to see where its mass came from.')

      const lean = el('pre', 'pg-lean', functorForm(this.leanState()))
      // what Lean makes of the state: its normal form
      const ln = el('div', 'pg-lean-state')
      if (!BACKEND) ln.textContent = tr('Lean is not connected: the board checks for every p by itself, without Lean.')
      else if (!this.leanNow) ln.textContent = tr('Lean is normalising …')
      else if (this.leanNow.error) ln.textContent = `Lean: ${this.leanNow.error.message}`
      else {
        ln.append(el('span', 'pg-lean-label', tr('Lean:') + ' '), el('code', '', functorForm(this.leanNow.result)))
        if (sameDist(d, this.target) && this.leanAgrees() === false) ln.append(el('div', 'pg-warn', `${tr('Lean disagrees: the target is')} ${functorForm(this.leanGoal.result)}`))
      }
      // the task, in words, and the target as a picture of its own (always, also on another space)
      const task = el('div', 'pg-task')
      const tk = axis(this.target.space, [...this.target.mass.keys()]).filter(k => !(this.target.mass.get(k) ?? ZERO).zero)
      task.append(el('b', '', tr('Task: bring the distribution into the shape of the target') + (this.count ? ' (' + tr('in exactly {n} moves', { n: this.count }) + ')' : '') + ': '),
        tk.length === 1 && (this.target.mass.get(tk[0]) ?? ZERO).eq(ONE) ? tr('surely {b}', { b: pointName(this.target.space, tk[0]) })
          : tk.map(k => `P(${pointName(this.target.space, k)}) = ${this.target.mass.get(k)}`).join(', '))
      const row = el('div', 'pg-row')
      row.append(s, this.targetPicture())
      // the example p of the picture
      const slider = el('label', 'pg-slider')
      const input = el('input'); input.type = 'range'; input.min = '0.05'; input.max = '0.95'; input.step = '0.05'; input.value = String(P)
      input.addEventListener('input', () => { P = Number(input.value); try { localStorage.setItem('pg:p', input.value) } catch {}; this.render() })
      slider.append(`${tr('the picture for p =')} ${P.toFixed(2)} `, input, el('span', 'pg-slider-note', ' ' + tr('(only an example; the masses hold for every p)')))
      const parts = [task, row, slider, this.info, ...(SHOW ? [] : [ln]), el('div', 'pg-moves-head', tr('Moves')), moves, tools, ...(SHOW ? [] : [lean])]
      if (done) {
        const box = el('div', 'pg-solved')
        box.append(el('div', 'pg-solved-head', 'goals accomplished 🎉' + (this.leanAgrees() ? ` (${tr('confirmed by Lean, for every p')})` : '')))
        // what Lean has confirmed: the moves played are the target, for every p (or, without Lean, the
        // statement of the level, proved in Proofs/)
        const statement = this.leanAgrees() ? `${functorForm(this.leanState())} = ${functorForm(this.leanGoal.result)}` : this.leanStatement
        if (statement && !SHOW) {
          box.append(el('div', 'pg-solved-lean-head', tr('In Lean, for every p:')))
          box.append(el('pre', 'pg-lean', statement))
        }
        const next = el('button', 'pg-next', tr(this.root.dataset.proof && !SHOW ? 'To the proof ›' : 'Next level ›'))
        next.type = 'button'
        next.addEventListener('click', () => this.onNext?.())
        box.append(next)
        parts.push(box)
      }
      showBoard(this, parts)
    }
  }

  // ---------------------------------------------------------------- the building site

  // A level of the building site (`::::build`): the player lays down coins, all with the same p and
  // independent of each other, and applies functions to one or several of them; each result is a new
  // node, to which functions apply again. A coin may feed several functions, so the nodes form a
  // network, which runs into the target. "Check" compares the distribution of the chosen node (the
  // one selected, or else the newest) with the target, exactly, for every p. The distribution of a
  // node is found by going through all outcomes of the coins below it.

  // The functions: their arity (a number, or the least number of inputs), the space of their inputs and
  // of their value, the value, and the forms for the card and for Lean.
  const FUNS = {
    not: { sym: '¬', arity: 1, from: 'bool', to: 'bool', f: ([a]) => !a, show: ([a]) => `¬${a}`, lean: ([a]) => `!${a}`, label: 'not' },
    and: { sym: '∧', arity: 2, more: true, from: 'bool', to: 'bool', f: xs => xs.every(x => x), show: xs => xs.join(' ∧ '), lean: xs => xs.join(' && '), label: 'and' },
    or: { sym: '∨', arity: 2, more: true, from: 'bool', to: 'bool', f: xs => xs.some(x => x), show: xs => xs.join(' ∨ '), lean: xs => xs.join(' || '), label: 'or' },
    xor: { sym: '⊕', arity: 2, more: true, from: 'bool', to: 'bool', f: xs => xs.filter(x => x).length % 2 === 1, show: xs => xs.join(' ⊕ '),
      lean: xs => xs.slice(1).reduce((e, x) => `xor (${e}) ${x}`, xs[0]), label: 'xor' },
    toNat: { sym: 'ℕ', arity: 1, from: 'bool', to: 'nat', f: ([a]) => (a ? 1 : 0), show: ([a]) => `𝟙(${a})`, lean: ([a]) => `${a}.toNat`, label: 'toNat: false = 0, true = 1' },
    count: { sym: '#', arity: 1, more: true, from: 'bool', to: 'nat', f: xs => xs.filter(x => x).length, show: xs => `#(${xs.join(', ')})`,
      lean: xs => `[${xs.join(', ')}].count true`, label: 'number of true' },
    add: { sym: '+', arity: 2, more: true, from: 'nat', to: 'nat', f: xs => xs.reduce((a, b) => a + b, 0), show: xs => xs.join(' + '), lean: xs => xs.join(' + '), label: 'add' },
    pos: { sym: '≥1', arity: 1, from: 'nat', to: 'bool', f: ([a]) => a >= 1, show: ([a]) => `${a} ≥ 1`, lean: ([a]) => `decide (1 ≤ ${a})`, label: 'at least 1' },
    max: { sym: 'max', arity: 2, more: true, from: 'nat', to: 'nat', f: xs => Math.max(...xs), show: xs => `max(${xs.join(', ')})`,
      lean: xs => xs.slice(1).reduce((e, x) => `max (${e}) ${x}`, xs[0]), label: 'maximum' },
  }
  Object.assign(DE, {
    not: 'nicht', and: 'und', or: 'oder', xor: 'genau eins', add: 'addieren',
    'number of true': 'Anzahl true', 'at least 1': 'mindestens 1', maximum: 'Maximum', 'p-coin': 'p-Münze', Functions: 'Funktionen', Check: 'Prüfen', 'Remove the last': 'Letztes entfernen',
    '{n} left': 'noch {n}', 'Building blocks': 'Bausteine',
    'Lay down a coin with “p-coin”. Tap lines to choose them (in this order), then a function.': 'Leg mit „p-Münze“ eine Münze hin. Tippe Leitungen an, um sie auszuwählen (in dieser Reihenfolge), dann eine Funktion.',
    'Choose {n} lines first (tap them).': 'Wähle erst {n} Leitungen aus (antippen).', 'Choose at least {n} lines first (tap them).': 'Wähle erst mindestens {n} Leitungen aus (antippen).',
    'This function needs coins (true/false).': 'Diese Funktion braucht Münzen (true/false).', 'This function needs numbers.': 'Diese Funktion braucht Zahlen.',
    'No more of these in this level.': 'Davon gibt es in diesem Level keine weiteren.', 'There is nothing to check yet.': 'Es gibt noch nichts zu prüfen.',
    'Checked: {x}. It lives on {a}, the target on {b}.': 'Geprüft: {x}. Es lebt auf {a}, das Ziel auf {b}.',
    'Checked: {x}. At {k} it has P = {m}, the target {t}.': 'Geprüft: {x}. Bei {k} hat es P = {m}, das Ziel {t}.',
    'Checked: {x}, the selected line (or else the newest).': 'Geprüft wird {x}: die ausgewählte Leitung (sonst die neueste).',
    'As a do block in Lean:': 'Als do-Block in Lean:',
    'Task: build the target:': 'Aufgabe: Bau das Ziel:',
  })
  // The sources: a coin, or a binomial B(n, p), each new one independent of the others.
  const choose = (n, k) => { let r = 1; for (let i = 0; i < k; i++) r = r * (n - i) / (i + 1); return r }
  const pow = (m, k) => { let r = ONE; for (let i = 0; i < k; i++) r = r.mul(m); return r }
  const source = spec => {
    if (spec === 'coin') return { space: 'bool', prefix: 'M', lean: 'coin p', label: () => tr('p-coin'),
      outcomes: () => [[false, complement(PP)], [true, PP]] }
    const n = Number(/^binom(\d+)$/.exec(spec)?.[1])
    if (n) return { space: 'nat', prefix: 'B', lean: `binom p ${n}`, label: () => `B(${n}, p)`,
      outcomes: () => Array.from({ length: n + 1 }, (_, k) => [k, new Poly([new Q(choose(n, k))]).mul(pow(PP, k)).mul(pow(complement(PP), n - k))]) }
    throw new Error(`unknown source ${spec}`)
  }
  const funLabel = f => `${FUNS[f].sym}  ${tr(FUNS[f].label)}`
  const COLORS = ['#b0782a', '#2e6fb8', '#8e44ad', '#c0392b', '#16a085', '#d35400', '#34495e', '#7d6608']

  class Builder {
    constructor(root, index, onSolved) {
      this.root = root; this.index = index; this.onSolved = onSolved
      this.target = parseDist(root.dataset.target)
      this.funs = root.dataset.moves.split(',').map(x => x.trim()).filter(x => FUNS[x])
      // the sources offered, with how many of each (`coin:3, binom2:2`; no number: as many as wanted)
      this.sources = (root.dataset.sources || `coin:${root.dataset.coins || ''}`).split(',').map(x => {
        const [k, m] = x.trim().split(':'); return { spec: k, max: Number(m || 0) || Infinity }
      })
      this.board = root.querySelector('.pg-board')
      this.key = `pg:${location.pathname}:${index}`
      // { src } (a source) or { fun, inputs: [indices] }: the sources of the level lie there from the
      // start (as many of each as the level has), the functions come after them
      this.nodes = this.initial()
      try {
        const saved = JSON.parse(localStorage.getItem(this.key + ':tree') ?? 'null')
        if (saved && JSON.stringify(saved.slice(0, this.nodes.length)) === JSON.stringify(this.nodes)) this.nodes = saved
      } catch {}
      this.selected = []   // indices, in the order chosen
      this.checked = null  // { node, ok }
      this.message = ''
      // a tap beside the lines (or Escape) chooses none
      document.addEventListener('click', e => {
        if (!this.selected.length || !this.root.offsetParent || e.target.closest?.('.pg-card, button, input, a, .pg-tip-overlay')) return
        this.selected = []; this.message = ''; this.render()
      })
      // Escape chooses none; Delete (or Backspace) deletes what is chosen
      document.addEventListener('keydown', e => {
        if (!this.selected.length || !this.root.offsetParent || document.querySelector('.pg-tip-overlay') || e.target.closest?.('input, textarea')) return
        if (e.key === 'Escape') { this.selected = []; this.message = ''; this.render() }
        if (e.key === 'Delete' || e.key === 'Backspace') { e.preventDefault(); this.remove() }
      })
      this.render()
    }

    // the sources the level starts with: all of each that has a number (those without one are laid
    // down with a button, as many as wanted)
    initial() { return this.sources.flatMap(src => (src.max < Infinity ? Array.from({ length: src.max }, () => ({ src: src.spec })) : [])) }

    get solved() { try { return localStorage.getItem(this.key) === '1' } catch { return false } }
    save() { try { localStorage.setItem(this.key + ':tree', JSON.stringify(this.nodes)) } catch {} }

    // names: coins M1, M2, …; binomials B1, …; results Z1, Z2, …
    prefix(i) { const n = this.nodes[i]; return n.src ? source(n.src).prefix : 'Z' }
    name(i) { return this.prefix(i) + this.nodes.slice(0, i + 1).filter((_, j) => this.prefix(j) === this.prefix(i)).length }
    space(i) { const n = this.nodes[i]; return n.src ? source(n.src).space : FUNS[n.fun].to }
    // the nodes below i (with i), in their order
    below(i) {
      const seen = new Set(), go = j => { if (seen.has(j)) return; seen.add(j); (this.nodes[j].inputs ?? []).forEach(go) }
      go(i)
      return [...seen].sort((a, b) => a - b)
    }
    // the outcomes of node j, given the values of its inputs: [value, mass] (a function has one, of mass 1;
    // a coin two; later sources and random functions (kernels) more)
    outcomes(j, val) {
      const n = this.nodes[j]
      if (n.src) return source(n.src).outcomes()
      return [[FUNS[n.fun].f(n.inputs.map(k => val.get(k))), ONE]]
    }
    // the distribution of node i: the nodes below it, one after the other as in a do block, each
    // branching over its outcomes
    dist(i) {
      const order = this.below(i), mass = new Map(), val = new Map()
      const go = (k, w) => {
        if (k === order.length) { const v = String(val.get(i)); mass.set(v, (mass.get(v) ?? ZERO).add(w)); return }
        for (const [v, m] of this.outcomes(order[k], val)) { val.set(order[k], v); go(k + 1, w.mul(m)) }
      }
      go(0, ONE)
      for (const [k, m] of mass) if (m.zero) mass.delete(k)
      return { space: this.space(i), mass }
    }
    // the formula of a result, in the names of its inputs
    formula(i) { const n = this.nodes[i]; return n.src ? '' : FUNS[n.fun].show(n.inputs.map(j => this.name(j))) }
    // node i as a do block of DiscreteMeasure
    lean(i) {
      const lines = this.below(i).map(j => {
        const n = this.nodes[j], x = this.name(j).toLowerCase()
        return n.src ? `  let ${x} ← ${source(n.src).lean}` : `  let ${x} := ${FUNS[n.fun].lean(n.inputs.map(k => this.name(k).toLowerCase()))}`
      })
      return ['do', ...lines, `  return ${this.name(i).toLowerCase()}`].join('\n')
    }

    changed() { this.checked = null; this.message = ''; this.save(); this.render() }
    left(src) { return src.max - this.nodes.filter(n => n.src === src.spec).length }
    addSource(src) {
      if (this.left(src) <= 0) { this.message = tr('No more of these in this level.'); this.render(); return }
      this.nodes.push({ src: src.spec }); this.changed()
    }
    apply(f) {
      const F = FUNS[f], sel = this.selected
      const bad = sel.length < F.arity || (!F.more && sel.length > F.arity) ? tr(F.more ? 'Choose at least {n} lines first (tap them).' : 'Choose {n} lines first (tap them).', { n: F.arity })
        : sel.some(j => this.space(j) !== F.from) ? tr(F.from === 'bool' ? 'This function needs coins (true/false).' : 'This function needs numbers.') : null
      if (bad) { this.message = bad; this.render(); return }
      this.nodes.push({ fun: f, inputs: sel.slice() }); this.selected = []; this.changed()
    }
    pick(i) {
      const k = this.selected.indexOf(i)
      if (k >= 0) this.selected.splice(k, 1); else this.selected.push(i)
      this.message = ''; this.render()
    }
    // Deletes the chosen lines and all that is built on them. The coins of the level stay (they
    // belong to it): for a chosen coin, what is built on it goes.
    remove() {
      if (!this.selected.length) return
      const fixed = this.initial().length, chosen = new Set(this.selected), gone = new Set()
      this.nodes.forEach((n, j) => {
        if ((chosen.has(j) && !(n.src && j < fixed)) || n.inputs?.some(k => gone.has(k) || chosen.has(k))) gone.add(j)
      })
      this.selected = []
      if (!gone.size) { this.message = tr('The coins of the level stay; nothing is built on this one yet.'); this.render(); return }
      const keep = this.nodes.map((_, j) => j).filter(j => !gone.has(j)), at = new Map(keep.map((j, k) => [j, k]))
      this.nodes = keep.map(j => { const n = this.nodes[j]; return n.inputs ? { ...n, inputs: n.inputs.map(k => at.get(k)) } : n })
      this.changed()
    }
    removeLast() { if (!this.canUndo) return; this.nodes.pop(); this.selected = this.selected.filter(j => j < this.nodes.length); this.changed() }
    reset() { this.nodes = this.initial(); this.selected = []; this.changed() }
    undo() { this.removeLast() }
    get canUndo() { return this.nodes.length > this.initial().length }
    status() {
      if (this.checked?.ok) return 'goals accomplished 🎉'
      if (!this.nodes.length) return tr('Lay down a building block.')
      if (this.selected.length) return tr('{n} chosen: now a function, Check, or Delete.', { n: this.selected.length })
      return tr('Tap lines to choose them, then a function. Check compares a line with the target.')
    }

    check() {
      if (!this.nodes.length) { this.message = tr('There is nothing to check yet.'); this.render(); return }
      const i = this.selected.length === 1 ? this.selected[0] : this.nodes.length - 1
      const d = this.dist(i), t = this.target, x = this.name(i)
      const ok = sameDist(d, t)
      this.checked = { node: i, ok }
      if (ok) {
        this.message = ''
        const first = !this.solved
        try { localStorage.setItem(this.key, '1') } catch {}
        this.onSolved?.(first)
      } else if (d.space !== t.space) this.message = tr('Checked: {x}. It lives on {a}, the target on {b}.', { x, a: spaceName(d.space), b: spaceName(t.space) })
      else {
        const k = axis(t.space, [...d.mass.keys(), ...t.mass.keys()]).find(k => !(d.mass.get(k) ?? ZERO).eq(t.mass.get(k) ?? ZERO))
        this.message = tr('Checked: {x}. At {k} it has P = {m}, the target {t}.', { x, k: pointName(t.space, k), m: String(d.mass.get(k) ?? ZERO), t: String(t.mass.get(k) ?? ZERO) })
      }
      this.render()
    }

    // a small picture of a distribution, at (x, y): its width is returned
    chart(g, d, x, y, cls) {
      const ks = axis(d.space, [...d.mass.keys()])
      const gap = Math.max(46, ...ks.map(k => String(d.mass.get(k) ?? ZERO).length * 6 + 8)), w = Math.max(96, gap * ks.length), base = y + 14, bh = 30
      const x0 = x + w / 2 - (gap * (ks.length - 1)) / 2, bw = Math.min(26, gap - 14)
      const c = svg('g', { class: 'pg-mini ' + cls })
      c.append(svg('line', { x1: x, x2: x + w, y1: base, y2: base, class: 'pg-axis-thin' }))
      ks.forEach((k, j) => {
        const m = d.mass.get(k) ?? ZERO, xx = x0 + j * gap, hh = m.value(P) * bh
        if (hh > 0) c.append(svg('rect', { class: 'pg-mini-mass', x: xx - bw / 2, y: base - hh, width: bw, height: hh, rx: 2 }))
        c.append(svg('text', { x: xx, y: base - hh - 3, 'text-anchor': 'middle', class: 'pg-mini-mass' }, m.toString()))
        c.append(svg('text', { x: xx, y: base + 12, 'text-anchor': 'middle', class: 'pg-mini-point' }, pointName(d.space, k)))
      })
      g.append(c)
      return w
    }

    // The circuit: a line per node (coins and results), in the order they were made; a column per
    // function, with a dot on each line it takes, ending in a box with its symbol, from which its
    // result runs on as a new line. At the end of each line, its distribution. Lines a column only
    // crosses carry no dot (and the column passes over them).
    circuit() {
      const RH = 64, TOP = 14, LAB = 40, GW = 50, n = this.nodes.length
      const funs = this.nodes.map((m, i) => (m.src ? -1 : i)).filter(i => i >= 0)
      const col = i => funs.indexOf(i)
      // where a line starts: a result at its column, a coin after the columns made before it
      const start = i => this.nodes[i].src ? LAB + this.nodes.slice(0, i).filter(m => !m.src).length * GW : LAB + col(i) * GW + GW / 2 + 13
      const xe = LAB + funs.length * GW + 14, y = i => TOP + i * RH + RH / 2
      const focus = this.checked?.ok ? new Set(this.below(this.checked.node))
        : this.selected.length ? new Set(this.selected.flatMap(j => this.below(j))) : null
      const dim = i => (focus && !focus.has(i) ? ' pg-dim' : '')
      const g = svg('g')
      const dists = this.nodes.map((_, i) => this.dist(i))
      // the rows: a band to tap, the name, the line, the distribution
      let wmax = 0
      const rows = svg('g'), cols = svg('g'), charts = svg('g')
      this.nodes.forEach((m, i) => {
        const sel = this.selected.indexOf(i), ok = this.checked?.ok && focus.has(i), bad = this.checked && !this.checked.ok && this.checked.node === i
        const row = svg('g', { class: 'pg-card' + (sel >= 0 ? ' pg-card-sel' : '') + (ok ? ' pg-card-ok' : '') + (bad ? ' pg-card-bad' : '') + dim(i), 'data-node': i })
        row.append(svg('rect', { class: 'pg-row-band', x: 0, y: y(i) - RH / 2 + 2, width: 10, height: RH - 4, rx: 8 }))
        row.append(svg('text', { x: 8, y: y(i) + 5, class: 'pg-row-name', fill: COLORS[i % COLORS.length] }, this.name(i)))
        if (sel >= 0) {
          row.append(svg('circle', { cx: LAB - 6, cy: y(i) - 14, r: 8, class: 'pg-row-badge' }))
          row.append(svg('text', { x: LAB - 6, y: y(i) - 10.5, 'text-anchor': 'middle', class: 'pg-row-badge-text' }, String(sel + 1)))
        }
        row.append(svg('line', { x1: start(i), x2: xe, y1: y(i), y2: y(i), class: 'pg-line', stroke: COLORS[i % COLORS.length] }))
        if (m.src) row.append(svg('circle', { cx: start(i), cy: y(i), r: 5, class: 'pg-source', fill: COLORS[i % COLORS.length] }))
        const t = el('title'); t.textContent = m.src ? `${this.name(i)} ← ${source(m.src).lean}` : `${this.name(i)} = ${this.formula(i)}`; row.append(t)
        row.addEventListener('click', () => this.pick(i))
        rows.append(row)
        wmax = Math.max(wmax, this.chart(charts, dists[i], xe + 12, y(i) - RH / 2 + 8, (ok ? 'pg-ok' : '') + dim(i)))
      })
      // the columns: a halo where they pass over lines, the dots on their inputs, the box
      funs.forEach(i => {
        const m = this.nodes[i], x = LAB + col(i) * GW + GW / 2, top = Math.min(...m.inputs.map(y)), c = COLORS[i % COLORS.length]
        const cg = svg('g', { class: 'pg-colm' + dim(i) })
        cg.append(svg('line', { x1: x, x2: x, y1: top, y2: y(i) - 12, class: 'pg-colm-halo' }))
        cg.append(svg('line', { x1: x, x2: x, y1: top, y2: y(i) - 12, class: 'pg-colm-line', stroke: c }))
        for (const j of m.inputs) cg.append(svg('circle', { cx: x, cy: y(j), r: 5.5, class: 'pg-dot-in', fill: COLORS[j % COLORS.length] }))
        const sym = FUNS[m.fun].sym, bw = Math.max(24, sym.length * 9 + 8)
        cg.append(svg('rect', { x: x - bw / 2, y: y(i) - 12, width: bw, height: 24, rx: 6, class: 'pg-gate', stroke: c }))
        cg.append(svg('text', { x, y: y(i) + 5, 'text-anchor': 'middle', class: 'pg-gate-sym' }, sym))
        cols.append(cg)
      })
      g.append(rows, cols, charts)
      // checked: an arrow from the end of the line, towards the target
      const W = xe + 12 + wmax + 40
      rows.querySelectorAll('.pg-row-band').forEach(b => b.setAttribute('width', W))
      if (this.checked) {
        const yy = y(this.checked.node)
        g.append(svg('text', { x: W - 30, y: yy + 6, class: this.checked.ok ? 'pg-arrow-ok' : 'pg-arrow-bad' }, this.checked.ok ? '✓ ▶' : '✗'))
      }
      const s = svg('svg', { viewBox: `0 0 ${W} ${TOP + n * RH + 6}`, class: 'pg-circuit', width: W })
      s.append(g)
      return s
    }

    render() {
      const done = this.checked?.ok
      // the task
      const task = el('div', 'pg-task'), t = this.target
      const tk = axis(t.space, [...t.mass.keys()]).filter(k => !(t.mass.get(k) ?? ZERO).zero)
      task.append(el('b', '', tr('Task: build the target:') + ' '),
        tk.length === 1 && (t.mass.get(tk[0]) ?? ZERO).eq(ONE) ? tr('surely {b}', { b: pointName(t.space, tk[0]) })
          : tk.map(k => `P(${pointName(t.space, k)}) = ${t.mass.get(k)}`).join(', '))

      // the building blocks
      const blocks = el('div', 'pg-blocks')
      blocks.append(el('div', 'pg-moves-head', tr('Functions')))
      for (const src of this.sources) {
        if (src.max < Infinity) continue
        const b = el('button', 'pg-move pg-coin-btn', '+ ' + source(src.spec).label() + (src.max < Infinity ? ` (${tr('{n} left', { n: this.left(src) })})` : ''))
        b.type = 'button'; b.disabled = this.left(src) <= 0
        b.addEventListener('click', () => this.addSource(src))
        blocks.append(b)
      }
      for (const f of this.funs) {
        const F = FUNS[f], fits = this.selected.length >= F.arity && (F.more || this.selected.length === F.arity) && this.selected.every(j => this.space(j) === F.from)
        const b = el('button', 'pg-move' + (fits ? '' : ' pg-move-off'), funLabel(f))
        b.type = 'button'
        b.addEventListener('click', () => this.apply(f))
        blocks.append(b)
      }

      // the circuit, and the target beside it
      const site = el('div', 'pg-site')
      site.append(this.nodes.length ? this.circuit() : el('div', 'pg-site-empty', tr('Lay down a coin with “p-coin”. Tap lines to choose them (in this order), then a function.')))
      this.targetBox = el('div', 'pg-target-box' + (done ? ' pg-card-ok' : ''))
      this.targetBox.append(this.targetPicture())
      const area = el('div', 'pg-build-area')
      area.append(site, this.targetBox)

      const tools = el('div', 'pg-tools')
      const check = el('button', 'pg-check', tr('Check')), undo = el('button', 'pg-tool', '↶ ' + tr('Remove the last')), reset = el('button', 'pg-tool', '⟲ ' + tr('Start over'))
      const del = el('button', 'pg-delete', '🗑 ' + tr('Delete'))
      check.type = undo.type = reset.type = del.type = 'button'
      undo.disabled = reset.disabled = !this.canUndo
      del.disabled = !this.selected.length
      del.title = tr('Deletes the chosen lines, and what is built on them.')
      del.addEventListener('click', () => this.remove())
      check.addEventListener('click', () => this.check())
      undo.addEventListener('click', () => this.removeLast()); reset.addEventListener('click', () => this.reset())
      tools.append(check, del, undo, reset)

      const now = this.selected.length === 1 ? this.selected[0] : this.nodes.length - 1
      const info = el('div', 'pg-info' + (this.message ? ' pg-warn' : ''),
        this.message || (this.nodes.length ? tr('Checked: {x}, the selected line (or else the newest).', { x: this.name(now) + (this.nodes[now].src ? '' : ` = ${this.formula(now)}`) }) : ''))

      const slider = el('label', 'pg-slider')
      const input = el('input'); input.type = 'range'; input.min = '0.05'; input.max = '0.95'; input.step = '0.05'; input.value = String(P)
      input.addEventListener('input', () => { P = Number(input.value); try { localStorage.setItem('pg:p', input.value) } catch {}; this.render() })
      slider.append(`${tr('the picture for p =')} ${P.toFixed(2)} `, input, el('span', 'pg-slider-note', ' ' + tr('(only an example; the masses hold for every p)')))

      const parts = [task, blocks, area, tools, info, slider]
      if (done) {
        const box = el('div', 'pg-solved')
        box.append(el('div', 'pg-solved-head', 'goals accomplished 🎉'))
        if (!SHOW) {
          box.append(el('div', 'pg-solved-lean-head', tr('As a do block in Lean:')))
          box.append(el('pre', 'pg-lean', this.lean(this.checked.node)))
        }
        const next = el('button', 'pg-next', tr(this.root.dataset.proof && !SHOW ? 'To the proof ›' : 'Next level ›'))
        next.type = 'button'
        next.addEventListener('click', () => this.onNext?.())
        box.append(next)
        parts.push(box)
      }
      showBoard(this, parts)
    }
  }
  Builder.prototype.targetPicture = Level.prototype.targetPicture

  // ---------------------------------------------------------------- world 0: walking on the grid

  // A level of world 0 (`::::walk`): a figure on the grid ℤ × ℤ, moved by north, east, south, west
  // (sure moves) and step (all four ways). In the monad Id it is at one point; in Set at all the
  // points it can reach. Lean normalises the walk `pure (0, 0) >>= north >>= …` after each move,
  // in Lean/World0.lean; its normal form is `pure (x, y)` or a set `{(x, y), …}`, read back as points.
  // The level is solved when the points are the target and Lean agrees.
  const RULES0 = 'pure_bind, north, south, east, west, step, Set.pure_def, ProbGame.singleton_bind, ProbGame.insert_bind, ' +
    'Set.singleton_union, Set.insert_union, Set.insert_eq_of_mem, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, ' +
    'zero_add, add_zero, Int.reduceAdd, Int.reduceSub, Int.reduceNeg, Int.reduceEq, eq_self_iff_true, and_self, and_true, true_and, ' +
    'and_false, false_and, or_true, true_or, or_false, false_or'
  const STEPS = { north: [[0, 1]], south: [[0, -1]], east: [[1, 0]], west: [[-1, 0]], step: [[1, 0], [-1, 0], [0, 1], [0, -1]] }
  Object.assign(DE, {
    '↑ north': '↑ Norden', '↓ south': '↓ Süden', '→ east': '→ Osten', '← west': '← Westen', '✳ step: all four ways': '✳ step: alle vier Richtungen',
    'A wall is in the way.': 'Da ist eine Wand im Weg.', 'Task: bring the figure to the flag.': 'Aufgabe: Bring die Figur zur Fahne.',
    'Task: reach exactly the marked points ({n}).': 'Aufgabe: Erreiche genau die markierten Punkte ({n}).',
    'In Lean:': 'In Lean:', 'confirmed by Lean': 'von Lean bestätigt',
    'Tap a point to see its coordinates.': 'Tippe einen Punkt an, um seine Koordinaten zu sehen.',
    '{n} points': '{n} Punkte', 'dark: x + y odd': 'dunkel: x + y ungerade', 'light: x + y even': 'hell: x + y gerade',
    'The figure moves with sure moves only; step needs the monad Set.': 'Die Figur geht nur mit sicheren Zügen; step braucht die Monade Set.',
  })
  const LABEL0 = { north: '↑ north', south: '↓ south', east: '→ east', west: '← west', step: '✳ step: all four ways' }
  const key0 = (x, y) => `${x},${y}`
  const point0 = k => k.split(',').map(Number)
  // a target: points `x,y x,y …`, or `walk n`, the points after n steps
  function parseTarget0(spec) {
    const m = /^walk (\d+)$/.exec(spec.trim())
    if (m) {
      const n = Number(m[1]), r = new Set()
      for (let x = -n; x <= n; x++) for (let y = -n; y <= n; y++) if (Math.abs(x) + Math.abs(y) <= n && (x + y + n) % 2 === 0) r.add(key0(x, y))
      return r
    }
    return new Set(spec.trim().split(/\s+/).filter(Boolean))
  }
  // the points of a normal form `pure (1, 2)` or `{(1, 0), (-1, 0)}`; null when it is something else
  function readPoints0(s) {
    const t = s.replace(/\s+/g, ' ').trim()
    if (!/^(pure \(-?\d+, -?\d+\)|\{\(-?\d+, -?\d+\)(, \(-?\d+, -?\d+\))*\})$/.test(t)) return null
    return new Set([...t.matchAll(/\((-?\d+), (-?\d+)\)/g)].map(m => key0(m[1], m[2])))
  }
  const sameSet = (a, b) => a.size === b.size && [...a].every(k => b.has(k))

  class Grid {
    constructor(root, index, onSolved) {
      this.root = root; this.index = index; this.onSolved = onSolved
      const d = root.dataset
      this.monad = d.monad === 'Set' ? 'Set' : 'Id'
      this.start = d.start || '0,0'
      this.target = parseTarget0(d.target)
      this.walls = new Set((d.walls ?? '').split(/\s+/).filter(Boolean))
      this.colours = !!d.colours
      this.moves = d.moves.split(',').map(s => s.trim()).filter(m => STEPS[m])
      this.context = d.context ?? ''
      this.board = root.querySelector('.pg-board')
      this.key = `pg:${location.pathname}:${index}`
      this.steps = []; this.picked = null; this.leanNow = null
      this.pts = new Set([this.start])
      // the part of the grid shown: start, target and walls, with a margin; it grows when the points leave it
      const all = [this.start, ...this.target, ...this.walls].map(point0)
      this.box = [Math.min(-2, ...all.map(p => p[0])) - 1, Math.max(2, ...all.map(p => p[0])) + 1, Math.min(-2, ...all.map(p => p[1])) - 1, Math.max(2, ...all.map(p => p[1])) + 1]
      this.updateLean()
      this.render()
    }

    get solved() { try { return localStorage.getItem(this.key) === '1' } catch { return false } }

    // the walk as Lean writes it
    leanState() { return `pure (${this.start.replace(',', ', ')}) >>= ${this.steps.join(' >>= ')}`.replace(/ >>= $/, '') }
    leanExpr() { return `(${this.leanState()} : ${this.monad} Pos)` }
    updateLean() {
      const expr = this.leanExpr()
      this.leanNow = null
      normalise(this.context, expr, { open: '', vars: '', rules: RULES0 }).then(r => {
        if (this.leanExpr() === expr) { this.leanNow = r; this.render(); this.check() }
      })
    }
    // the points of Lean's normal form; whether they are the target (null while Lean is asked)
    leanPoints() { return this.leanNow?.result ? readPoints0(this.leanNow.result) : null }
    leanAgrees() {
      if (!BACKEND) return null
      const p = this.leanPoints()
      return p ? sameSet(p, this.target) : null
    }
    get done() { return sameSet(this.pts, this.target) && (!BACKEND || this.leanAgrees() === true) }

    play(name) {
      if (this.animating) return
      if (this.monad === 'Id' && name === 'step') { this.flash(tr('The figure moves with sure moves only; step needs the monad Set.')); return }
      const next = new Set()
      for (const k of this.pts) { const [x, y] = point0(k); for (const [dx, dy] of STEPS[name]) next.add(key0(x + dx, y + dy)) }
      if ([...next].some(k => this.walls.has(k))) { this.flash(tr('A wall is in the way.')); return }
      const before = this.pts
      this.steps.push(name); this.picked = null
      this.updateLean()
      this.animate(before, name, () => { this.pts = next; this.render(); this.check() })
    }
    recompute() {
      let pts = new Set([this.start])
      for (const s of this.steps) {
        const next = new Set()
        for (const k of pts) { const [x, y] = point0(k); for (const [dx, dy] of STEPS[s]) next.add(key0(x + dx, y + dy)) }
        pts = next
      }
      this.pts = pts
    }
    undo() { if (this.animating || !this.steps.length) return; this.steps.pop(); this.recompute(); this.picked = null; this.updateLean(); this.render() }
    reset() { if (this.animating) return; this.steps = []; this.recompute(); this.picked = null; this.updateLean(); this.render() }
    get canUndo() { return this.steps.length > 0 }
    status() {
      if (this.done) return 'goals accomplished 🎉'
      if (!this.steps.length) return tr('Tap a move.')
      if (sameSet(this.pts, this.target)) return tr('Lean is checking …')
      return this.monad === 'Id' ? tr('Not at the flag yet.') : tr('{n} points; the target has {m}.', { n: this.pts.size, m: this.target.size })
    }

    check() {
      if (this.animating || !this.done) return
      const first = !this.solved
      try { localStorage.setItem(this.key, '1') } catch {}
      this.render()
      this.onSolved?.(first)
    }
    flash(text) { this.info.textContent = text; this.info.classList.add('pg-warn'); setTimeout(() => this.info.classList.remove('pg-warn'), 1200) }

    // the geometry: a cell per point of the box, y upwards
    geometry() {
      for (const k of this.pts) {
        const [x, y] = point0(k)
        this.box = [Math.min(this.box[0], x - 1), Math.max(this.box[1], x + 1), Math.min(this.box[2], y - 1), Math.max(this.box[3], y + 1)]
      }
      const [x0, x1, y0, y1] = this.box, cols = x1 - x0 + 1, rows = y1 - y0 + 1
      const c = Math.min(46, 520 / cols)
      return { c, w: cols * c, h: rows * c, cx: x => (x - x0 + 0.5) * c, cy: y => (y1 - y + 0.5) * c }
    }

    // each point moves to its images (300 ms)
    animate(before, name, done) {
      const g = this.geometry(), layer = svg('g', { class: 'pg-walk-flow' })
      this.svg.querySelectorAll('.pg-walk-pt, .pg-figure').forEach(e => e.classList.add('pg-fading'))
      const parts = []
      for (const k of before) {
        const [x, y] = point0(k)
        for (const [dx, dy] of STEPS[name]) {
          const e = this.monad === 'Id' ? svg('circle', { class: 'pg-figure', r: g.c * 0.32 }) : svg('circle', { class: 'pg-walk-pt', r: g.c * 0.2 })
          layer.append(e); parts.push({ e, x0: g.cx(x), y0: g.cy(y), x1: g.cx(x + dx), y1: g.cy(y + dy) })
        }
      }
      this.svg.append(layer)
      this.animating = true
      const t0 = performance.now(), T = matchMedia?.('(prefers-reduced-motion: reduce)').matches ? 1 : 350
      const frame = now => {
        const t = Math.min(1, (now - t0) / T), e = t < 0.5 ? 2 * t * t : 1 - (-2 * t + 2) ** 2 / 2
        for (const p of parts) { p.e.setAttribute('cx', p.x0 + (p.x1 - p.x0) * e); p.e.setAttribute('cy', p.y0 + (p.y1 - p.y0) * e) }
        if (t < 1) requestAnimationFrame(frame)
        else { this.animating = false; done() }
      }
      requestAnimationFrame(frame)
    }

    render() {
      const done = this.done, g = this.geometry(), [x0, x1, y0, y1] = this.box
      const s = svg('svg', { viewBox: `0 0 ${g.w} ${g.h}`, class: 'pg-svg pg-grid' + (done ? ' pg-done' : '') })
      for (let x = x0; x <= x1; x++) for (let y = y0; y <= y1; y++) {
        const k = key0(x, y), dark = this.colours && Math.abs(x + y) % 2 === 1
        const cell = svg('rect', { class: 'pg-cell' + (dark ? ' pg-cell-dark' : '') + (this.walls.has(k) ? ' pg-wall' : '') + (x === 0 && y === 0 ? ' pg-home' : ''),
          x: (x - x0) * g.c, y: (y1 - y) * g.c, width: g.c, height: g.c })
        cell.addEventListener('click', () => { this.picked = this.picked === k ? null : k; this.render() })
        s.append(cell)
      }
      // the target: a flag (Id), or rings (Set)
      for (const k of this.target) {
        const [x, y] = point0(k)
        if (this.monad === 'Id') s.append(svg('text', { class: 'pg-flag', x: g.cx(x), y: g.cy(y) + g.c * 0.22, 'text-anchor': 'middle', 'font-size': g.c * 0.62 }, '⚑'))
        else s.append(svg('circle', { class: 'pg-walk-target', cx: g.cx(x), cy: g.cy(y), r: g.c * 0.34 }))
      }
      for (const k of this.pts) {
        const [x, y] = point0(k)
        const e = this.monad === 'Id' ? svg('circle', { class: 'pg-figure', cx: g.cx(x), cy: g.cy(y), r: g.c * 0.32 })
          : svg('circle', { class: 'pg-walk-pt' + (this.target.has(k) ? '' : ' pg-walk-off'), cx: g.cx(x), cy: g.cy(y), r: g.c * 0.2 })
        e.addEventListener('click', () => { this.picked = this.picked === k ? null : k; this.render() })
        s.append(e)
      }
      if (this.picked) { const [x, y] = point0(this.picked); s.append(svg('rect', { class: 'pg-cell-picked', x: (x - x0) * g.c + 2, y: (y1 - y) * g.c + 2, width: g.c - 4, height: g.c - 4, rx: 4 })) }
      this.svg = s

      const moves = el('div', 'pg-moves')
      for (const m of this.moves) {
        const b = el('button', 'pg-move' + (this.monad === 'Id' && m === 'step' ? ' pg-move-off' : ''), tr(LABEL0[m]))
        b.type = 'button'; b.title = m
        b.addEventListener('click', () => this.play(m))
        moves.append(b)
      }
      const tools = el('div', 'pg-tools')
      const undo = el('button', 'pg-tool', '↶ ' + tr('Undo')), reset = el('button', 'pg-tool', '⟲ ' + tr('Start over'))
      undo.type = reset.type = 'button'
      undo.disabled = reset.disabled = !this.steps.length
      undo.addEventListener('click', () => this.undo()); reset.addEventListener('click', () => this.reset())
      tools.append(undo, reset)

      this.info = el('div', 'pg-info')
      if (this.picked) {
        const [x, y] = point0(this.picked)
        this.info.textContent = `(${x}, ${y})` + (this.colours ? ` · ${tr(Math.abs(x + y) % 2 ? 'dark: x + y odd' : 'light: x + y even')}` : '') +
          (this.monad === 'Set' ? ` · ${this.pts.has(this.picked) ? '∈' : '∉'}` : '')
      } else this.info.textContent = this.monad === 'Set' ? `${tr('{n} points', { n: this.pts.size })} · ${tr('Tap a point to see its coordinates.')}` : tr('Tap a point to see its coordinates.')

      const ln = el('div', 'pg-lean-state')
      if (!BACKEND) ln.textContent = tr('Lean is not connected: the board checks by itself, without Lean.')
      else if (!this.leanNow) ln.textContent = tr('Lean is normalising …')
      else if (this.leanNow.error) ln.textContent = `Lean: ${this.leanNow.error.message}`
      else {
        ln.append(el('span', 'pg-lean-label', tr('Lean:') + ' '), el('code', '', this.leanNow.result.replace(/\s+/g, ' ')))
        const p = this.leanPoints()
        if (p && sameSet(this.pts, this.target) && !sameSet(p, this.target)) ln.append(el('div', 'pg-warn', tr('Lean disagrees.')))
      }
      const task = el('div', 'pg-task')
      task.append(el('b', '', this.monad === 'Id' ? tr('Task: bring the figure to the flag.') : tr('Task: reach exactly the marked points ({n}).', { n: this.target.size })))
      const parts = [task, s, this.info, ...(SHOW ? [] : [ln]), el('div', 'pg-moves-head', tr('Moves')), moves, tools, ...(SHOW ? [] : [el('pre', 'pg-lean', this.leanState())])]
      if (done) {
        const box = el('div', 'pg-solved')
        box.append(el('div', 'pg-solved-head', 'goals accomplished 🎉' + (this.leanAgrees() ? ` (${tr('confirmed by Lean')})` : '')))
        if (this.leanAgrees()) {
          box.append(el('div', 'pg-solved-lean-head', tr('In Lean:')))
          box.append(el('pre', 'pg-lean', `${this.leanState()} = ${this.leanNow.result.replace(/\s+/g, ' ')}`))
        }
        const next = el('button', 'pg-next', tr(this.root.dataset.proof && !SHOW ? 'To the proof ›' : 'Next level ›'))
        next.type = 'button'
        next.addEventListener('click', () => this.onNext?.())
        box.append(next)
        parts.push(box)
      }
      showBoard(this, parts)
    }
  }
  Object.assign(DE, {
    'Lean is not connected: the board checks by itself, without Lean.': 'Lean ist nicht verbunden: Das Spielfeld prüft selbst, aber ohne Lean.',
    'Lean disagrees.': 'Lean widerspricht.',
  })

  // ---------------------------------------------------------------- the first world: true and false

  // A coin lies surely on one side, once for each input (one row, or two rows: for every b); a move is
  // a map Bool → Bool. Lean normalises the value or the map after each move (`RULESB`).
  const RULESB = 'id_eq, Bool.not_not, Bool.not_true, Bool.not_false'
  const arg = e => (/^\w+$/.test(e) ? e : `(${e})`)
  const MOVESB = {
    not: { f: b => !b, lean: e => `!${arg(e)}`, label: 'not: swap the sides' },
    true: { f: () => true, lean: e => `(fun _ => true) ${arg(e)}`, label: 'always true' },
    false: { f: () => false, lean: e => `(fun _ => false) ${arg(e)}`, label: 'always false' },
  }
  Object.assign(DE, {
    'Task: lay the coin on the flag.': 'Aufgabe: Leg die Münze auf die Fahne.',
    'Task: lay each coin on its flag.': 'Aufgabe: Leg jede Münze auf ihre Fahne.',
    'in exactly {n} moves': 'in genau {n} Zügen',
    '{n} moves so far': 'bisher {n} Züge',
    'Too many moves: undo, or start over.': 'Zu viele Züge: zurücknehmen oder neu anfangen.',
    'for b = {b}': 'für b = {b}', 'start': 'Start',
  })
  class Bools {
    constructor(root, index, onSolved) {
      this.root = root; this.index = index; this.onSolved = onSolved
      const d = root.dataset
      this.inputs = d.inputs.split(/\s+/).filter(Boolean).map(x => x === 'true')
      this.target = d.target.split(/\s+/).filter(Boolean).map(x => x === 'true')
      this.moves = d.moves.split(',').map(s => s.trim()).filter(m => MOVESB[m])
      this.count = Number(d.count) || 0
      this.context = d.context ?? ''
      this.board = root.querySelector('.pg-board')
      this.key = `pg:${location.pathname}:${index}`
      this.steps = []; this.leanNow = null
      this.updateLean()
      this.render()
    }
    get solved() { try { return localStorage.getItem(this.key) === '1' } catch { return false } }
    get rows() { return this.inputs.length > 1 }
    // where each coin lies now
    get values() { return this.inputs.map(b => this.steps.reduce((v, m) => MOVESB[m].f(v), b)) }
    // the moves as Lean writes them: the value (one row), or the map (for every b)
    leanState() {
      const e = this.steps.reduce((e, m) => MOVESB[m].lean(e), this.rows ? 'b' : String(this.inputs[0]))
      return this.rows ? `fun (b : Bool) => ${e}` : e
    }
    updateLean() {
      if (!this.steps.length) { this.leanNow = null; return }
      const expr = `id (${this.leanState()})`
      this.leanNow = null
      normalise(this.context, expr, { open: '', vars: '', rules: RULESB }).then(r => {
        if (this.steps.length && `id (${this.leanState()})` === expr) { this.leanNow = r; this.render(); this.check() }
      })
    }
    // the values of Lean's normal form, `true` or `fun b => !b`
    leanValues() {
      const r = this.leanNow?.result?.replace(/\s+/g, ' ').trim()
      if (!r) return null
      const body = this.rows ? /^fun b => (.*)$/.exec(r)?.[1] : r
      const val = (t, b) => t === 'true' ? true : t === 'false' ? false : t === 'b' ? b : t === '!b' ? !b : null
      return this.inputs.map(b => val(body, b))
    }
    leanAgrees() {
      if (!BACKEND) return null
      const v = this.leanValues()
      return v ? v.every((x, i) => x === this.target[i]) : null
    }
    get onTarget() { return this.values.every((x, i) => x === this.target[i]) }
    get done() {
      return this.steps.length > 0 && (!this.count || this.steps.length === this.count) && this.onTarget &&
        (!BACKEND || this.leanAgrees() === true)
    }

    play(m) {
      if (this.animating) return
      if (this.count && this.steps.length >= this.count) { this.flash(tr('Too many moves: undo, or start over.')); return }
      const before = this.values
      this.steps.push(m)
      this.updateLean()
      this.animate(before, this.values, () => { this.render(); this.check() })
    }
    undo() { if (this.animating || !this.steps.length) return; this.steps.pop(); this.updateLean(); this.render() }
    reset() { if (this.animating) return; this.steps = []; this.updateLean(); this.render() }
    get canUndo() { return this.steps.length > 0 }
    status() {
      if (this.done) return 'goals accomplished 🎉'
      if (!this.steps.length) return tr('Tap a move.')
      if (this.count && this.steps.length > this.count) return tr('Too many moves: undo, or start over.')
      if (this.onTarget) return this.count && this.steps.length !== this.count ? tr('On the flag, but in {n} moves, please.', { n: this.count }) : tr('Lean is checking …')
      return this.count ? tr('{n} moves so far', { n: this.steps.length }) + ' · ' + tr('not on the flag yet.') : tr('Not on the flag yet.')
    }
    check() {
      if (this.animating || !this.done) return
      const first = !this.solved
      try { localStorage.setItem(this.key, '1') } catch {}
      this.render()
      this.onSolved?.(first)
    }
    flash(text) { this.info.textContent = text; this.info.classList.add('pg-warn'); setTimeout(() => this.info.classList.remove('pg-warn'), 1200) }

    // a row per input: its label, and the two sides false | true
    geometry() { const c = 64, lw = this.rows ? 92 : 64; return { c, lw, w: lw + 2 * c, h: this.inputs.length * c, cx: v => lw + (v ? 1.5 : 0.5) * c, cy: i => (i + 0.5) * c } }
    // the coins slide to their new sides (350 ms)
    animate(before, after, done) {
      const g = this.geometry()
      const coins = [...this.svg.querySelectorAll('.pg-figure')]
      this.animating = true
      const t0 = performance.now(), T = matchMedia?.('(prefers-reduced-motion: reduce)').matches ? 1 : 350
      const frame = now => {
        const t = Math.min(1, (now - t0) / T), e = t < 0.5 ? 2 * t * t : 1 - (-2 * t + 2) ** 2 / 2
        coins.forEach((c, i) => c.setAttribute('cx', g.cx(before[i]) + (g.cx(after[i]) - g.cx(before[i])) * e))
        if (t < 1) requestAnimationFrame(frame)
        else { this.animating = false; done() }
      }
      requestAnimationFrame(frame)
    }

    render() {
      const done = this.done, g = this.geometry(), values = this.values
      const s = svg('svg', { viewBox: `0 0 ${g.w} ${g.h + 22}`, class: 'pg-svg pg-grid pg-bools' + (done ? ' pg-done' : '') })
      this.inputs.forEach((b, i) => {
        const y = i * g.c
        s.append(svg('text', { class: 'pg-bool-label', x: 4, y: g.cy(i) + 5 }, this.rows ? tr('for b = {b}', { b }) : tr('start')))
        for (const v of [false, true]) s.append(svg('rect', { class: 'pg-cell' + (v === b ? ' pg-home' : ''), x: g.lw + (v ? g.c : 0), y, width: g.c, height: g.c }))
        s.append(svg('text', { class: 'pg-flag', x: g.cx(this.target[i]) + g.c * 0.3, y: g.cy(i) - g.c * 0.16, 'text-anchor': 'middle', 'font-size': g.c * 0.36 }, '⚑'))
        s.append(svg('circle', { class: 'pg-figure', cx: g.cx(values[i]), cy: g.cy(i), r: g.c * 0.26 }))
      })
      for (const v of [false, true]) s.append(svg('text', { class: 'pg-bool-side', x: g.cx(v), y: g.h + 16, 'text-anchor': 'middle' }, String(v)))
      this.svg = s

      const moves = el('div', 'pg-moves')
      for (const m of this.moves) {
        const b = el('button', 'pg-move', tr(MOVESB[m].label)); b.type = 'button'; b.title = m
        b.addEventListener('click', () => this.play(m))
        moves.append(b)
      }
      const tools = el('div', 'pg-tools')
      const undo = el('button', 'pg-tool', '↶ ' + tr('Undo')), reset = el('button', 'pg-tool', '⟲ ' + tr('Start over'))
      undo.type = reset.type = 'button'
      undo.disabled = reset.disabled = !this.steps.length
      undo.addEventListener('click', () => this.undo()); reset.addEventListener('click', () => this.reset())
      tools.append(undo, reset)
      this.info = el('div', 'pg-info', this.count ? tr('{n} moves so far', { n: this.steps.length }) : '')

      const ln = el('div', 'pg-lean-state')
      if (!BACKEND) ln.textContent = tr('Lean is not connected: the board checks by itself, without Lean.')
      else if (!this.steps.length) ln.append(el('span', 'pg-lean-label', tr('Lean:') + ' '), el('code', '', this.leanState()))
      else if (!this.leanNow) ln.textContent = tr('Lean is normalising …')
      else if (this.leanNow.error) ln.textContent = `Lean: ${this.leanNow.error.message}`
      else {
        ln.append(el('span', 'pg-lean-label', tr('Lean:') + ' '), el('code', '', this.leanNow.result.replace(/\s+/g, ' ')))
        if (this.onTarget && this.leanAgrees() === false) ln.append(el('div', 'pg-warn', tr('Lean disagrees.')))
      }
      const task = el('div', 'pg-task')
      task.append(el('b', '', tr(this.rows ? 'Task: lay each coin on its flag.' : 'Task: lay the coin on the flag.') +
        (this.count ? ' (' + tr('in exactly {n} moves', { n: this.count }) + ')' : '')))
      const parts = [task, s, this.info, ...(SHOW ? [] : [ln]), el('div', 'pg-moves-head', tr('Moves')), moves, tools, ...(SHOW ? [] : [el('pre', 'pg-lean', this.leanState())])]
      if (done) {
        const box = el('div', 'pg-solved')
        box.append(el('div', 'pg-solved-head', 'goals accomplished 🎉' + (this.leanAgrees() ? ` (${tr('confirmed by Lean')})` : '')))
        if (this.leanAgrees()) {
          box.append(el('div', 'pg-solved-lean-head', tr('In Lean:')))
          box.append(el('pre', 'pg-lean', `${this.leanState()} = ${this.leanNow.result.replace(/\s+/g, ' ')}`))
        }
        const next = el('button', 'pg-next', tr(this.root.dataset.proof && !SHOW ? 'To the proof ›' : 'Next level ›'))
        next.type = 'button'
        next.addEventListener('click', () => this.onNext?.())
        box.append(next)
        parts.push(box)
      }
      showBoard(this, parts)
    }
  }

  // ---------------------------------------------------------------- the proof

  // The second part of a level, as in the Natural Number Game: once the board is solved, its statement
  // is to be proved in Lean, one tactic after another (`/start` and `/check` of the bridge, in the
  // context Lean/Rules.lean). The inventory holds the tactics and rules introduced so far (by the
  // number of the level, `"2.3"`) and the lemmas proved in earlier levels; a line that uses anything
  // else is refused before Lean sees it.

  const INVENTORY = [
    { name: 'rw', kind: 'tactic', at: '1.1', w0: '0.1', wb: 'b.2', insert: 'rw []', sig: 'rw [h]   rw [← h]   rw [h₁, h₂]',
      en: 'Rewrites the goal with the equation h: its left side becomes its right side (with ←, the other way round). Closes the goal when it then reads a = a. It does not rewrite where names bound in a do block occur; there, use simp only.',
      de: 'Schreibt das Ziel mit der Gleichung h um: Ihre linke Seite wird zu ihrer rechten (mit ← umgekehrt). Schließt das Ziel, wenn es danach a = a lautet. Es schreibt nicht dort um, wo in einem do-Block gebundene Namen vorkommen; dort hilft simp only.' },
    { name: 'apply', kind: 'tactic', at: '1.1', w0: '0.5', insert: 'apply ', sig: 'apply h',
      en: 'For a goal that is the conclusion of the rule h: leaves what h needs (its hypotheses) as the new goals.',
      de: 'Für ein Ziel, das die Folgerung der Regel h ist: lässt das, was h braucht (ihre Annahmen), als neue Ziele.' },
    { name: 'rfl', kind: 'tactic', at: '1.4', w0: '0.1', wb: 'b.1', insert: 'rfl', sig: 'rfl',
      en: 'Closes a goal a = b whose sides are the same after computing (!true is false, 1 + 1 is 2).',
      de: 'Schließt ein Ziel a = b, dessen Seiten nach Ausrechnen gleich sind (!true ist false, 1 + 1 ist 2).' },
    { name: 'congr', kind: 'tactic', at: '1.5', insert: 'congr 1', sig: 'congr 1',
      en: 'For a goal f a = f b, or μ >>= g = μ >>= h (a do block): reduces it to the parts that differ (a = b, g = h).',
      de: 'Für ein Ziel f a = f b, oder μ >>= g = μ >>= h (ein do-Block): führt es auf die Teile zurück, die sich unterscheiden (a = b, g = h).' },
    { name: 'funext', kind: 'tactic', at: '1.5', wb: 'b.5', insert: 'funext x', sig: 'funext x',
      en: 'For a goal g = h between functions: it suffices that g x = h x for every x.',
      de: 'Für ein Ziel g = h zwischen Funktionen: Es genügt, dass g x = h x für jedes x.' },
    { name: 'cases', kind: 'tactic', at: '1.3', w0: '0.8', wb: 'b.4', insert: 'cases x', sig: 'cases x   cases h : f x',
      enb: 'Splits into the cases of x: for x : Bool, the goals for false and for true, one after the other. cases h : f x splits into the cases of the value of f x and keeps the case as the hypothesis h.',
      deb: 'Teilt in die Fälle von x: für x : Bool die Ziele für false und für true, eines nach dem anderen. cases h : f x teilt in die Fälle des Werts von f x und behält den Fall als Annahme h.',
      en0: 'Splits a hypothesis h into its cases. For h : false = true there is no case: the goal is done.',
      de0: 'Teilt eine Annahme h in ihre Fälle. Für h : false = true gibt es keinen Fall: Das Ziel ist erledigt.',
      en: 'Splits into the cases of x: for x : Bool, the goals for false and for true, one after the other.',
      de: 'Teilt in die Fälle von x: für x : Bool die Ziele für false und für true, eines nach dem anderen.' },
    { name: 'simp only', kind: 'tactic', at: '2.4', w0: '0.2', insert: 'simp only []', sig: 'simp only [h₁, h₂, …]',
      en: 'Rewrites with the given rules everywhere, also inside do blocks, as often as it can; closes the goal when both sides become the same.',
      de: 'Schreibt mit den angegebenen Regeln überall um, auch in do-Blöcken, so oft es geht; schließt das Ziel, wenn beide Seiten gleich werden.' },
    { name: '<;>', kind: 'tactic', at: '3.6', wb: 'b.4', insert: ' <;> ', sig: 't₁ <;> t₂',
      en: 'Runs t₂ on every goal that t₁ leaves: cases x <;> cases y <;> rfl.',
      de: 'Führt t₂ auf jedem Ziel aus, das t₁ übrig lässt: cases x <;> cases y <;> rfl.' },
    { name: "induction'", kind: 'tactic', at: '4.3', w0: '0.7', insert: "induction' n with n ih", sig: "induction' n with n ih",
      en: 'Induction on the natural number n: first the goal for 0, then the goal for n + 1, with the hypothesis ih for n.',
      de: 'Induktion nach der natürlichen Zahl n: zuerst das Ziel für 0, dann das Ziel für n + 1, mit der Annahme ih für n.' },
    { name: 'bool_ext', kind: 'rule', at: '1.1', sig: 'bool_ext μ ν (h : μ true = ν true) : μ = ν', en: 'Two distributions on Bool are the same when they have the same mass at true.', de: 'Zwei Verteilungen auf Bool sind gleich, wenn sie bei true dieselbe Masse haben.' },
    { name: 'coin_true', kind: 'rule', at: '1.1', sig: '(coin p) true = ↑p', en: 'The mass of the coin at true.', de: 'Die Masse der Münze bei true.' },
    { name: 'coin_false', kind: 'rule', at: '1.2', sig: '(coin p) false = ↑(σ p)', en: 'The mass of the coin at false.', de: 'Die Masse der Münze bei false.' },
    { name: 'map_true', kind: 'rule', at: '1.2', sig: '(f <$> μ) true = (bif f true then μ true else 0) + (bif f false then μ false else 0)', en: 'Where the mass of a move goes: to true comes the mass of the points that f sends to true.', de: 'Wohin die Masse eines Zuges geht: Nach true kommt die Masse der Punkte, die f nach true schickt.' },
    { name: 'Bool.not_true', kind: 'rule', at: '1.2', wb: 'b.2', sig: '(!true) = false', en: 'Not true is false.', de: 'Nicht true ist false.' },
    { name: 'Bool.not_false', kind: 'rule', at: '1.2', wb: 'b.2', sig: '(!false) = true', en: 'Not false is true.', de: 'Nicht false ist true.' },
    { name: 'Bool.cond_true', kind: 'rule', at: '1.2', sig: '(bif true then a else b) = a', en: 'bif with true: the first.', de: 'bif mit true: das Erste.' },
    { name: 'Bool.cond_false', kind: 'rule', at: '1.2', sig: '(bif false then a else b) = b', en: 'bif with false: the second.', de: 'bif mit false: das Zweite.' },
    { name: 'zero_add', kind: 'rule', at: '1.2', sig: '0 + n = n', en: 'Adding to zero.', de: 'Zu null addieren.' },
    { name: 'coin_not_true', kind: 'lemma', at: '1.2', sig: '(not <$> coin p) true = ↑(σ p)', en: 'Proved by you in One Coin, level 2.', de: 'Von dir bewiesen in „Eine Münze“, Level 2.' },
    { name: 'coin_not', kind: 'lemma', at: '1.8', sig: 'not <$> coin p = coin (σ p)', en: 'Proved by you: the boss of One Coin. Flipping a coin swaps the masses.', de: 'Von dir bewiesen: der Endgegner von „Eine Münze“. Umdrehen tauscht die Massen.' },
    { name: 'coin_total', kind: 'rule', at: '1.3', sig: '(coin p) true + (coin p) false = 1', en: 'The total mass of a coin is one.', de: 'Die Gesamtmasse einer Münze ist eins.' },
    { name: 'pure_true', kind: 'rule', at: '1.3', sig: '(pure b) true = bif b then 1 else 0', en: 'The mass of a point mass at true.', de: 'Die Masse einer Punktmasse bei true.' },
    { name: 'coin_const', kind: 'lemma', at: '1.3', sig: '(fun _ => b) <$> coin p = pure b', en: 'Proved by you in One Coin, level 3: a constant move sends all the mass to one point.', de: 'Von dir bewiesen in „Eine Münze“, Level 3: Ein konstanter Zug schickt die ganze Masse an einen Punkt.' },
    { name: 'map_pure', kind: 'rule', at: '1.4', w0: '0.7', sig: 'f <$> pure a = pure (f a)', en0: 'A move on a sure point moves the point.', de0: 'Ein Zug auf einem sicheren Punkt verschiebt den Punkt.', en: 'A move on a point mass moves the point.', de: 'Ein Zug auf einer Punktmasse verschiebt den Punkt.' },
    { name: 'map_map', kind: 'rule', at: '1.6', w0: '0.6', sig: 'g <$> (f <$> μ) = (fun x => g (f x)) <$> μ', sig0: 'g <$> (f <$> s) = (fun x => g (f x)) <$> s', en: 'Two moves are one move.', de: 'Zwei Züge sind ein Zug.' },
    { name: 'coin_and', kind: 'rule', at: '3.1', sig: '(do let x ← coin p; let y ← coin q; pure (x && y)) = coin (p * q)', en: 'Independence: both true with probability p · q.', de: 'Unabhängigkeit: beide true mit Wahrscheinlichkeit p · q.' },
    { name: 'bind_map_left', kind: 'rule', at: '2.5', sig: '(do let x ← f <$> μ; g x) = (do let x ← μ; g (f x))', en: 'A move on a throw goes into the result.', de: 'Ein Zug auf einem Wurf wandert ins Ergebnis.' },
    { name: 'map_bind', kind: 'rule', at: '3.3', w0: '0.6', sig0: 'f <$> (s >>= g) = s >>= fun a => f <$> g a', en0: 'A move after a walk goes into it.', de0: 'Ein Zug nach einem Weg wandert in ihn hinein.', sig: 'f <$> (do let x ← μ; g x) = (do let x ← μ; f <$> g x)', en: 'A move after a do block goes into it.', de: 'Ein Zug nach einem do-Block wandert in ihn hinein.' },
    { name: 'or_eq', kind: 'rule', at: '3.3', sig: '(x || y) = !(!x && !y)', en: 'De Morgan.', de: 'De Morgan.' },
    { name: 'Bool.and_not_self', kind: 'rule', at: '3.4', sig: '(x && !x) = false', en: 'Never both x and not x.', de: 'Nie zugleich x und nicht x.' },
    { name: 'coin_unused', kind: 'rule', at: '3.4', sig: '(do let _ ← coin p; ν) = ν', en: 'A coin whose result is not used changes nothing.', de: 'Eine Münze, deren Ergebnis nicht benutzt wird, ändert nichts.' },
    { name: 'Bool.or_not_self', kind: 'rule', at: '3.5', sig: '(x || !x) = true', en: 'Always x or not x.', de: 'Immer x oder nicht x.' },
    { name: 'binom_zero', kind: 'rule', at: '3.7', sig: 'binom p 0 = pure 0', en: 'The definition of binom: no throw.', de: 'Die Definition von binom: kein Wurf.' },
    { name: 'binom_succ', kind: 'rule', at: '3.7', sig: 'binom p (n + 1) = do let X ← coin p; let Y ← binom p n; pure (X.toNat + Y)', en: 'The definition of binom: one throw more.', de: 'Die Definition von binom: ein Wurf mehr.' },
    { name: 'bind_assoc', kind: 'rule', at: '2.4', sig: '(do let y ← (do let x ← μ; f x); g y) = (do let x ← μ; let y ← f x; g y)', en: 'A do block in a do block is one do block.', de: 'Ein do-Block in einem do-Block ist ein do-Block.' },
    { name: 'pure_bind', kind: 'rule', at: '2.2', w0: '0.1', sig: '(do let x ← pure a; f x) = f a', sig0: 'pure a >>= f = f a',
      en0: 'Starting at a, then f: that is f at a.', de0: 'In a anfangen, dann f: Das ist f bei a.', en: 'Throwing a point mass is no throw.', de: 'Eine Punktmasse zu werfen ist kein Wurf.' },
    { name: 'add_zero', kind: 'rule', at: '3.7', sig: 'n + 0 = n', en: 'Adding zero.', de: 'Null addieren.' },
    { name: 'add_assoc', kind: 'rule', at: '4.1', sig: 'a + b + c = a + (b + c)', en: 'Brackets in sums.', de: 'Klammern in Summen.' },
    { name: 'map_eq_pure_bind', kind: 'rule', at: '2.1', w0: '0.6', sig: 'f <$> μ = do let x ← μ; pure (f x)', sig0: 'f <$> s = s >>= fun x => pure (f x)',
      en0: 'Applying f to every point, as a walk.', de0: 'f auf jeden Punkt anwenden, als Weg.', en: 'A move as a do block.', de: 'Ein Zug als do-Block.' },
    { name: 'bind_pure', kind: 'rule', at: '2.3', sig: '(μ >>= fun x => pure x) = μ', en: 'A throw whose result is the result.', de: 'Ein Wurf, dessen Ergebnis das Ergebnis ist.' },
    { name: 'binom_one', kind: 'lemma', at: '4.2', sig: 'Bool.toNat <$> coin p = binom p 1', en: 'Proved by you in Counting, level 2.', de: 'Von dir bewiesen in „Zählen“, Level 2.' },
    { name: "binom_succ'", kind: 'lemma', at: '4.3', sig: "(do let X ← binom p n; let Y ← coin p; pure (X + Y.toNat)) = binom p (n + 1)", en: 'Proved by you in Counting, level 3.', de: 'Von dir bewiesen in „Zählen“, Level 3.' },
    // the first world only
    { name: 'Bool.not_not', kind: 'lemma', wb: 'b.4', at: '1.2', sig: '(!(!b)) = b', en: 'Proved by you in True and False: flipped twice is not flipped.', de: 'Von dir bewiesen in „Wahr und falsch“: Zweimal umgedreht ist nicht umgedreht.' },
    { name: 'Function.comp_apply', kind: 'rule', wb: 'b.5', sig: '(g ∘ f) x = g (f x)', en: 'First f, then g.', de: 'Erst f, dann g.' },
    { name: 'id_eq', kind: 'rule', wb: 'b.5', sig: 'id a = a', en: 'id does nothing.', de: 'id tut nichts.' },
    // world 0 only
    { name: 'constructor', kind: 'tactic', w0: '0.5', insert: 'constructor', sig: 'constructor',
      en: 'For a goal A ∧ B: the two goals A and B, one after the other.', de: 'Für ein Ziel A ∧ B: die zwei Ziele A und B, eines nach dem anderen.' },
    { name: 'exists', kind: 'tactic', w0: '0.5', insert: 'exists ', sig: 'exists a',
      en: 'For a goal ∃ x, P x: names the x, and leaves P a.', de: 'Für ein Ziel ∃ x, P x: nennt das x und lässt P a übrig.' },
    { name: 'intro', kind: 'tactic', w0: '0.8', insert: 'intro h', sig: 'intro h',
      en: 'For a goal A → B (and a ∉ s, which is a ∈ s → False): assumes A as h, and leaves B.',
      de: 'Für ein Ziel A → B (und a ∉ s, das ist a ∈ s → False): nimmt A als h an und lässt B übrig.' },
    { name: 'have', kind: 'tactic', w0: '0.8', insert: 'have h2 := ', sig: 'have h2 := rule args',
      en: 'Adds a new fact h2 to the hypotheses, here a rule applied to its arguments.',
      de: 'Fügt den Annahmen eine neue Tatsache h2 hinzu, hier eine Regel, angewandt auf ihre Argumente.' },
    { name: 'north', kind: 'rule', w0: '0.1', sig: 'north (x, y) = pure (x, y + 1)', en: 'One step north.', de: 'Ein Schritt nach Norden.' },
    { name: 'east', kind: 'rule', w0: '0.1', sig: 'east (x, y) = pure (x + 1, y)', en: 'One step east.', de: 'Ein Schritt nach Osten.' },
    { name: 'south', kind: 'rule', w0: '0.1', sig: 'south (x, y) = pure (x, y - 1)', en: 'One step south.', de: 'Ein Schritt nach Süden.' },
    { name: 'west', kind: 'rule', w0: '0.1', sig: 'west (x, y) = pure (x - 1, y)', en: 'One step west.', de: 'Ein Schritt nach Westen.' },
    { name: 'step', kind: 'rule', w0: '0.4', sig: 'step (x, y) = {(x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1)}', en: 'One step, all four ways.', de: 'Ein Schritt, alle vier Richtungen.' },
    { name: 'step_east', kind: 'rule', w0: '0.5', sig: '(x + 1, y) ∈ step (x, y)', en: 'East is one of the ways of step.', de: 'Osten ist einer der Wege von step.' },
    { name: 'step_west', kind: 'rule', w0: '0.5', sig: '(x - 1, y) ∈ step (x, y)', en: 'West is one of the ways of step.', de: 'Westen ist einer der Wege von step.' },
    { name: 'mem_bind', kind: 'rule', w0: '0.5', sig: 'b ∈ s >>= f ↔ ∃ a ∈ s, b ∈ f a', en: 'Reachable: there is a way.', de: 'Erreichbar: Es gibt einen Weg.' },
    { name: 'odd_step', kind: 'rule', w0: '0.6', sig: 'odd <$> step p = pure (!odd p)', en: 'A step changes the colour.', de: 'Ein Schritt wechselt die Farbe.' },
    { name: 'walk_zero', kind: 'rule', w0: '0.7', sig: 'walk 0 = pure (0, 0)', en: 'No step.', de: 'Kein Schritt.' },
    { name: 'walk_succ', kind: 'rule', w0: '0.7', sig: 'walk (n + 1) = walk n >>= step', en: 'One step more.', de: 'Ein Schritt mehr.' },
    { name: 'Nat.bodd_succ', kind: 'rule', w0: '0.7', sig: '(n + 1).bodd = !n.bodd', en: 'Odd and even alternate.', de: 'Gerade und ungerade wechseln sich ab.' },
    { name: 'mem_map', kind: 'rule', w0: '0.8', sig: 'mem_map f (h : a ∈ s) : f a ∈ f <$> s', en: 'What lies in s lies, moved by f, in f <$> s.', de: 'Was in s liegt, liegt, mit f bewegt, in f <$> s.' },
    { name: 'odd_bind_step', kind: 'lemma', w0: '0.6', sig: 'odd <$> (μ >>= step) = not <$> (odd <$> μ)', en: 'Proved by you in Walking on the Grid, level 6.', de: 'Von dir bewiesen in „Gehen auf dem Gitter“, Level 6.' },
    { name: 'odd_walk', kind: 'lemma', w0: '0.7', sig: 'odd <$> walk n = pure n.bodd', en: 'Proved by you: the boss of Walking on the Grid.', de: 'Von dir bewiesen: der Endgegner von „Gehen auf dem Gitter“.' },
    { name: 'binom_add', kind: 'lemma', at: '4.5', sig: '(do let X ← binom p n; let Y ← binom p m; pure (X + Y)) = binom p (n + m)', en: 'Proved by you: the boss of Counting.', de: 'Von dir bewiesen: der Endgegner von „Zählen“.' },
  ]
  Object.assign(DE, {
    Proof: 'Beweis', 'Run': 'Ausführen', 'Inventory': 'Inventar', Tactics: 'Taktiken', Theorems: 'Sätze',
    'Goal': 'Ziel', 'goal {i} of {n}': 'Ziel {i} von {n}', 'Lean is thinking …': 'Lean denkt …',
    'Your lemma {x} is now in your inventory.': 'Dein Lemma {x} ist jetzt in deinem Inventar.',
    'To the proof ›': 'Zum Beweis ›', 'Insert': 'Einsetzen', 'Remove the last line': 'Letzte Zeile entfernen',
    'The proof needs Lean: open the game with ?backend=… (the address of a bridge).': 'Der Beweis braucht Lean: Öffne das Spiel mit ?backend=… (der Adresse einer Bridge).',
    'Lean cannot be reached: {e}': 'Lean ist nicht erreichbar: {e}',
    '{x} is not unlocked yet.': '{x} ist noch nicht freigeschaltet.',
    '{x} is not in your inventory.': '{x} ist nicht in deinem Inventar.',
    'This tactic is not in your inventory: {x}': 'Diese Taktik ist nicht in deinem Inventar: {x}',
    'Statement': 'Aussage', 'a tactic, e.g. rw [coin_true]': 'eine Taktik, z. B. rw [coin_true]', 'a tactic, e.g. rfl': 'eine Taktik, z. B. rfl', 'a tactic, e.g. rw [pure_bind]': 'eine Taktik, z. B. rw [pure_bind]',
    'Proved earlier; the proof is kept.': 'Schon bewiesen; der Beweis ist gespeichert.',
  })
  // Lean's messages, as the player sees the goals: short names, I for the unit interval; and in front of
  // the usual ones a sentence that says what to do
  const leanText = m => m.replace(/MeasureTheory\.DiscreteMeasure\./g, '').replace(/ProbGame\./g, '').replace(/↑I/g, 'I')
  const ADVICE = [
    [/Did not find an occurrence of the pattern/, 'The left side of the rule does not occur in the goal as it stands. (Where names of a do block occur, rw cannot rewrite; simp only can.)',
      'Die linke Seite der Regel kommt im Ziel so nicht vor. (Wo Namen eines do-Blocks vorkommen, kann rw nicht umschreiben; simp only kann es.)'],
    [/motive is not type correct/, 'rw cannot rewrite here; try simp only.', 'rw kann hier nicht umschreiben; versuche simp only.'],
    [/simp made no progress/, 'simp only found nothing to rewrite with these rules.', 'simp only hat mit diesen Regeln nichts gefunden, was es umschreiben kann.'],
    [/could not unify the conclusion of `@funext`/, 'funext needs a goal g = h between functions (first congr 1?).', 'funext braucht ein Ziel g = h zwischen Funktionen (vorher congr 1?).'],
    [/Tactic `rfl` failed/, 'The two sides are not the same, not even after computing.', 'Die beiden Seiten sind nicht gleich, auch nicht nach Ausrechnen.'],
    [/[Nn]o goals/, 'There is no goal left.', 'Es ist kein Ziel mehr übrig.'],
    [/Unknown (identifier|constant)/, 'Lean does not know this name.', 'Diesen Namen kennt Lean nicht.'],
    [/unexpected token|expected/, 'Lean cannot read this line: a typo?', 'Lean kann diese Zeile nicht lesen: ein Tippfehler?'],
  ]
  const advice = m => { const a = ADVICE.find(([r]) => r.test(m)); return a ? (LANG === 'de' ? a[2] : a[1]) : '' }
  Object.assign(DE, { 'What Lean says': 'Was Lean sagt' })
  const atLeast = (a, b) => { const [x, y] = a.split('.'), [u, v] = b.split('.'); return x === u ? Number(y) >= Number(v) : Number(x) > Number(u) }

  class Proof {
    constructor(level, onChange) {
      const root = level.root
      this.level = level; this.root = root; this.onChange = onChange
      this.no = root.dataset.no; this.statement = root.dataset.proof; this.lemma = root.dataset.lemma
      this.context = root.dataset.proofContext ?? ''
      this.key = level.key + ':proof'
      this.lines = []
      try { this.lines = JSON.parse(localStorage.getItem(this.key) ?? '[]') } catch {}
      this.goals = null; this.error = ''; this.busy = false; this.session = null; this.picked = null
      this.box = el('section', 'pg-proof')
      this.box.hidden = true
      this.texts = [...root.querySelectorAll(':scope > .pg-text > .pg-proof-text, :scope .pg-proof-text')]
      for (const t of this.texts) {
        // a paragraph that begins with “Tip.” is folded
        t.querySelectorAll('p').forEach(p => {
          const first = p.firstElementChild
          if (first && p.textContent.trimStart().startsWith(first.textContent) && /^(Tip|Tipp)\.$/.test(first.textContent.trim())) {
            const d = el('details', 'pg-tip'), s = el('summary', '', first.textContent.replace('.', ''))
            first.remove(); p.before(d); d.append(s, p)
          }
        })
      }
      root.append(this.box)
    }

    get proved() { try { return localStorage.getItem(this.key + 'd') === '1' } catch { return false } }
    get canUndo() { return !this.busy && this.lines.length > 0 }
    status() {
      if (!BACKEND) return ''
      if (this.done) return 'goals accomplished 🎉'
      if (this.busy) return tr('Lean is thinking …')
      if (this.error) return tr('Lean did not take the line: see why above the input.')
      if (!this.lines.length) return tr('Type a tactic, or tap one in the inventory.')
      const n = this.goals?.length ?? 0
      return n === 1 ? tr('One goal left.') : tr('{n} goals left.', { n })
    }
    // the inventory at this level: what was introduced up to here; the lemma of this level is not yet
    available(item) { const at = this.since(item); return !!at && atLeast(this.no, at) && !(item.kind === 'lemma' && at === this.no) }
    // where an item comes in: world 0 has an inventory of its own (`w0`), the other worlds share one (`at`)
    since(item) { return this.world0 ? item.w0 : this.worldB ? item.wb : item.at }
    get world0() { return this.no.startsWith('0.') }
    get worldB() { return this.no.startsWith('b.') }

    // shown once the board is solved
    update() {
      const show = this.level.solved
      if (show && this.box.hidden) { this.box.hidden = false; this.render() }
      else if (!show) this.box.hidden = true
      // Lean is asked only for the level shown
      if (show && !this.started && !this.root.hidden) { this.started = true; this.begin() }
    }
    focus() { this.box.scrollIntoView({ behavior: 'smooth', block: 'start' }); setTimeout(() => this.input?.focus({ preventScroll: true }), 400) }

    async post(path, body) {
      const r = await fetch(BACKEND.replace(/\/$/, '') + path, { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify(body) })
      return r.json()
    }
    async begin() {
      if (!BACKEND) { this.render(); return }
      this.busy = true; this.render()
      try {
        const r = await this.post('/start', { context: this.context, statement: `example ${this.statement}` })
        if (r.error) { this.error = r.error.message; this.goals = null }
        else { this.session = r.session; this.goals = r.state.goals; await this.check(this.lines, true) }
      } catch (e) { this.error = tr('Lean cannot be reached: {e}', { e: String(e) }) }
      this.busy = false; this.render()
    }
    // Lean on the proof `lines`: on success they become the proof, else the error is shown
    async check(lines, quiet = false) {
      let r = await this.post('/check', { session: this.session, proof: lines.join('\n') })
      if (r.error?.kind === 'session') { await this.begin(); return false }
      if (r.error) { this.error = r.error.message; return false }
      const bad = r.steps.flatMap(s => s.diags.filter(d => d.severity === 1).map(d => d.message.text))
      if (bad.length) {
        this.error = bad[0]
        if (quiet) { this.lines = lines.slice(0, Math.max(0, r.steps.length - 1)); this.goals = r.steps[r.steps.length - 1].goals.map(g => g.goal.text) }
        return false
      }
      this.lines = lines; this.error = ''
      this.goals = r.steps[r.steps.length - 1].goals.map(g => g.goal.text)
      try { localStorage.setItem(this.key, JSON.stringify(lines)) } catch {}
      if (r.completed && !this.proved) {
        try { localStorage.setItem(this.key + 'd', '1') } catch {}
        this.onChange?.()
      }
      this.done = r.completed
      return true
    }

    // the game's rules for a line: only tactics and theorems of the inventory
    refuse(line) {
      const local = new Set((this.goals ?? []).join('\n').split('\n').flatMap(l => (/^([^⊢:][^:]*?) :/.exec(l.trim())?.[1] ?? '').split(/\s+/)).filter(Boolean))
      if (/sorry|\?|DiscreteMeasure|MeasureTheory|ProbGame\./.test(line)) return tr('{x} is not in your inventory.', { x: line })
      const parts = line.split('<;>')
      if (parts.length > 1 && !this.available(INVENTORY.find(i => i.name === '<;>'))) return tr('This tactic is not in your inventory: {x}', { x: '<;>' })
      for (let t of parts) {
        t = t.trim()
        const tac = /^(rw|simp only|rfl|congr|funext|cases|induction'|exists|intro|have|apply|constructor)(?=\s|\[|$)/.exec(t)?.[1]
        const item = INVENTORY.find(i => i.name === tac)
        if (!item || !this.available(item)) return tr('This tactic is not in your inventory: {x}', { x: t.split(/\s/)[0] || t })
        // the rules: in brackets, or the term of `have h := rule args`
        const inside = tac === 'have' ? /:=(.*)$/.exec(t)?.[1]?.trim().split(/\s+/)[0] : tac === 'apply' ? t.slice(5).trim().split(/\s+/)[0] : /\[(.*)\]/.exec(t)?.[1]
        if ((tac === 'rw' || tac === 'simp only') && inside === undefined) return tr('This tactic is not in your inventory: {x}', { x: t })
        // each rule: its name is in the inventory (or a hypothesis of the goal, as ih), and so are the
        // names in its arguments
        for (const arg of (inside ?? '').split(',').map(a => a.replace('←', '').trim()).filter(Boolean)) {
          const ids = arg.match(/[A-Za-z_][\w.']*/g) ?? []
          for (const [k, id] of ids.entries()) {
            const it = INVENTORY.find(i => i.name === id)
            if (it && it.kind !== 'tactic' && !this.available(it)) return tr('{x} is not unlocked yet.', { x: id })
            if (!it && !local.has(id) && (k === 0 || /[._]/.test(id))) return tr('{x} is not in your inventory.', { x: id })
          }
        }
      }
      return null
    }

    async run() {
      const line = this.input.value.trim()
      if (!line || this.busy || !this.session) return
      const no = this.refuse(line)
      if (no) { this.error = no; this.render(); return }
      this.busy = true; this.render()
      try { if (await this.check([...this.lines, line])) this.typed = '' } catch (e) { this.error = tr('Lean cannot be reached: {e}', { e: String(e) }) }
      this.busy = false; this.render(); this.input?.focus({ preventScroll: true })
    }
    async back() {
      if (this.busy || !this.lines.length) return
      this.busy = true; this.render()
      await this.check(this.lines.slice(0, -1)); this.done = false
      this.busy = false; this.render()
    }
    // the proof from the start again: no lines (a proof found stays found)
    async restart() {
      if (this.busy || !this.lines.length) return
      this.busy = true; this.error = ''; this.typed = ''; this.render()
      try { await this.check([]) } catch (e) { this.error = tr('Lean cannot be reached: {e}', { e: String(e) }) }
      this.done = false
      this.busy = false; this.render(); this.input?.focus({ preventScroll: true })
    }
    // a tapped item goes into the input: a rule into the brackets of rw/simp only, or as rw [rule]
    insert(item) {
      let v = this.input.value
      if (item.kind === 'tactic') v = item.name === '<;>' ? v + item.insert : (v.trim() ? v : item.insert)
      else if (/^have \S+ :=\s*$/.test(v) || /^apply\s*$/.test(v)) v = v.replace(/\s*$/, ' ') + item.name + (v.startsWith('have') ? ' ' : '')
      else if (/\[[^\]]*$/.test(v) || /\[\s*\]$/.test(v)) v = v.replace(/\[\s*\]$/, '[').replace(/(\[.*\S)$/, '$1, ') + item.name + (v.endsWith('[') || /\[\s*\]$/.test(v) ? ']' : '')
      else if (/\[.*\]/.test(v)) v = v.replace(/\s*\]([^\]]*)$/, (m, rest) => (/\[\s*$/.test(v.slice(0, v.lastIndexOf(']'))) ? '' : ', ') + item.name + ']' + rest)
      else v = `rw [${item.name}]`
      this.input.value = this.typed = v
      this.input.focus({ preventScroll: true })
    }

    render() {
      if (this.box.hidden) return
      const head = el('h3', 'pg-proof-head', tr('Proof'))
      const stmt = el('pre', 'pg-proof-statement', `${this.lemma ? `theorem ${this.lemma}` : 'example'} ${this.statement}`)
      const parts = STAGE ? [head, stmt] : [head, ...this.texts, stmt]
      if (!BACKEND) { parts.push(el('div', 'pg-info pg-warn', tr('The proof needs Lean: open the game with ?backend=… (the address of a bridge).'))); this.box.replaceChildren(...parts); return }

      // the lines so far, and the goals now
      const hist = el('ol', 'pg-proof-lines')
      this.lines.forEach(l => hist.append(el('li', '', l)))
      const goals = el('div', 'pg-goals')
      if (this.done) goals.append(el('div', 'pg-proof-done', 'goals accomplished 🎉' + (this.lemma ? ' ' + tr('Your lemma {x} is now in your inventory.', { x: this.lemma }) : '')))
      else if (this.goals) this.goals.forEach((g, i) => {
        // the goal now; the others folded, one line each
        const box = el(i ? 'details' : 'div', 'pg-goal' + (i ? ' pg-goal-later' : ''))
        if (this.goals.length > 1) box.append(el(i ? 'summary' : 'div', 'pg-goal-no', tr('goal {i} of {n}', { i: i + 1, n: this.goals.length })))
        box.append(el('pre', '', leanText(g)))
        goals.append(box)
      })
      if (this.busy) goals.append(el('div', 'pg-info', tr('Lean is thinking …')))
      // an error: our sentence, and Lean's message (folded when there is a sentence)
      const err = el('div', 'pg-proof-error')
      err.hidden = !this.error
      if (this.error) {
        const msg = leanText(this.error), say = advice(msg)
        if (say) {
          const d = el('details'), sm = el('summary', '', tr('What Lean says'))
          d.append(sm, el('pre', '', msg))
          err.append(el('div', 'pg-proof-advice', say), d)
        } else err.append(el('pre', '', msg))
      }

      // the input
      const row = el('div', 'pg-proof-input')
      this.input = el('input'); this.input.type = 'text'; this.input.spellcheck = false; this.input.autocapitalize = 'off'; this.input.autocomplete = 'off'; this.input.enterKeyHint = 'go'; this.input.setAttribute('autocorrect', 'off')
      this.input.placeholder = this.world0 ? tr('a tactic, e.g. rw [pure_bind]') : this.worldB ? tr('a tactic, e.g. rfl') : tr('a tactic, e.g. rw [coin_true]')
      this.input.value = this.typed ?? ''
      this.input.addEventListener('input', () => { this.typed = this.input.value })
      this.input.addEventListener('keydown', e => { if (e.key === 'Enter') { e.preventDefault(); this.run() } })
      const run = el('button', 'pg-check', tr('Run')); run.type = 'button'; run.disabled = this.busy || this.done
      run.addEventListener('click', () => this.run())
      row.append(this.input, run)
      const tools = el('div', 'pg-tools')
      const back = el('button', 'pg-tool', '↶ ' + tr('Remove the last line')); back.type = 'button'; back.disabled = this.busy || !this.lines.length
      back.addEventListener('click', () => this.back())
      const again = el('button', 'pg-tool', '⟲ ' + tr('Start over')); again.type = 'button'; again.disabled = this.busy || !this.lines.length
      again.addEventListener('click', () => this.restart())
      tools.append(back, again)

      // the inventory
      const inv = el('div', 'pg-inventory')
      inv.append(el('div', 'pg-moves-head', tr('Inventory')))
      for (const [kind, title] of [['tactic', tr('Tactics')], ['rule', tr('Theorems')]]) {
        const group = el('div', 'pg-inv-group')
        group.append(el('span', 'pg-inv-title', title + ':'))
        for (const item of INVENTORY.filter(i => (kind === 'tactic' ? i.kind === 'tactic' : i.kind !== 'tactic') && this.available(i))) {
          const b = el('button', 'pg-chip' + (item.kind === 'lemma' ? ' pg-chip-lemma' : '') + (this.picked === item.name ? ' pg-chip-on' : '') + (this.since(item) === this.no ? ' pg-chip-new' : ''), item.name)
          b.type = 'button'
          b.addEventListener('click', () => { this.picked = this.picked === item.name ? null : item.name; this.render() })
          group.append(b)
        }
        inv.append(group)
      }
      const it = INVENTORY.find(i => i.name === this.picked)
      if (it) {
        const doc = el('div', 'pg-inv-doc')
        const w = this.world0 && it.sig0 ? '0' : '', text = this.world0 && it.en0 ? (LANG === 'de' ? it.de0 : it.en0) : this.worldB && it.enb ? (LANG === 'de' ? it.deb : it.enb) : (LANG === 'de' ? it.de : it.en)
        doc.append(el('code', 'pg-inv-sig', it['sig' + w]), el('div', '', text))
        const ins = el('button', 'pg-tool', tr('Insert')); ins.type = 'button'
        ins.addEventListener('click', () => this.insert(it))
        doc.append(ins)
        inv.append(doc)
      }

      parts.push(hist, goals, err)
      if (!this.done) parts.push(row)
      if (!STAGE) parts.push(tools)
      // on the stage: the proof on the left, the inventory in a column on the right (below on phones)
      if (STAGE) {
        const main = el('div', 'pg-proof-main'), side = el('div', 'pg-proof-side')
        main.append(...parts); side.append(inv)
        this.box.replaceChildren(main, side)
        this.level.onRendered?.()
        return
      }
      parts.push(inv)
      if (this.done && !STAGE) {
        const next = el('button', 'pg-next', tr('Next level ›')); next.type = 'button'
        next.addEventListener('click', () => this.level.onNextLevel?.())
        parts.push(next)
      }
      this.box.replaceChildren(...parts)
      this.level.onRendered?.()
    }
  }

  // ---------------------------------------------------------------- the stage

  // A world's page shows one level at a time, on a stage as high as the screen (as in the
  // Incredible Proof Machine): on top the world, the level and a dot per level (← → also go to the
  // previous and next level); in the middle the board, or the proof once the board is solved; below,
  // a line that says what to do next, and the tool bar: Undo, Start over, Lean, Tips, Proof/Board,
  // Next. No text above the board: the texts are under Tips. A level's text appears once, when the
  // level is first played (with the text of the world at the first level), and the text of its proof
  // when the proof is first opened; the moves and rules new in a level come with it.
  let STAGE = false
  Object.assign(DE, {
    'Tap a move.': 'Tippe einen Zug an.', 'The distribution lives on {a}, the target on {b}.': 'Die Verteilung lebt auf {a}, das Ziel auf {b}.',
    'The right shape, but in {n} moves, please.': 'Die richtige Form, aber bitte in {n} Zügen.', 'Lean is checking …': 'Lean prüft …',
    'At {k}: P = {m}, the target has {t}.': 'Bei {k}: P = {m}, das Ziel hat {t}.', 'Lean disagrees.': 'Lean widerspricht.',
    'Lay down a building block.': 'Leg einen Baustein hin.', '{n} chosen: now a function, Check, or Delete.': '{n} ausgewählt: jetzt eine Funktion, Prüfen oder Löschen.',
    'The coins of the level stay; nothing is built on this one yet.': 'Die Münzen des Levels bleiben; auf dieser ist noch nichts gebaut.', Delete: 'Löschen',
    'Deletes the chosen lines, and what is built on them.': 'Löscht die ausgewählten Leitungen und was auf ihnen gebaut ist.',
    'Tap lines to choose them, then a function. Check compares a line with the target.': 'Tippe Leitungen an, dann eine Funktion. Prüfen vergleicht eine Leitung mit dem Ziel.',
    'Not at the flag yet.': 'Noch nicht bei der Fahne.', '{n} points; the target has {m}.': '{n} Punkte; das Ziel hat {m}.',
    'On the flag, but in {n} moves, please.': 'Auf der Fahne, aber bitte in {n} Zügen.', 'not on the flag yet.': 'noch nicht auf der Fahne.', 'Not on the flag yet.': 'Noch nicht auf der Fahne.',
    'Lean did not take the line: see why above the input.': 'Lean hat die Zeile nicht genommen: warum, steht über der Eingabe.',
    'Type a tactic, or tap one in the inventory.': 'Tippe eine Taktik ein, oder tippe eine im Inventar an.', 'One goal left.': 'Noch ein Ziel.', '{n} goals left.': 'Noch {n} Ziele.',
    'Tips': 'Tipps', 'Tip': 'Tipp', 'Got it': 'Verstanden', 'Close': 'Schließen', 'Restart': 'Neu', 'Next': 'Weiter', 'Next ›': 'Weiter ›',
    'Next world ›': 'Nächste Welt ›', 'World': 'Welt', 'Board': 'Spielfeld', 'Proof ': 'Beweis', 'This world': 'Diese Welt',
    'New in this level': 'Neu in diesem Level', 'New in this proof': 'Neu in diesem Beweis', 'Solve the board first.': 'Erst das Spielfeld lösen.',
  })
  // What the moves and building blocks do, for the tips (by kind of board: level, bool, build, src, walk).
  const MOVE_DOC = {
    'level:not': ['Swaps the sides: the mass of false goes to true, and the other way round.', 'Tauscht die Seiten: Die Masse von false geht nach true und umgekehrt.'],
    'level:heads': ['All the mass goes to true: the result is sure.', 'Die ganze Masse geht nach true: Das Ergebnis ist sicher.'],
    'level:tails': ['All the mass goes to false: the result is sure.', 'Die ganze Masse geht nach false: Das Ergebnis ist sicher.'],
    'level:id': ['Does nothing: the mass stays where it is.', 'Tut nichts: Die Masse bleibt, wo sie ist.'],
    'level:toNat': ['From sides to numbers: false becomes 0, true becomes 1.', 'Von Seiten zu Zahlen: false wird 0, true wird 1.'],
    'level:payoff': ['A bet: true becomes the gain, false the loss.', 'Eine Wette: true wird zum Gewinn, false zum Verlust.'],
    'bool:not': ['Flips the coin: true becomes false, false becomes true.', 'Dreht die Münze um: true wird false, false wird true.'],
    'bool:true': ['Lays the coin on true, wherever it lay.', 'Legt die Münze auf true, wo immer sie lag.'],
    'bool:false': ['Lays the coin on false, wherever it lay.', 'Legt die Münze auf false, wo immer sie lag.'],
    'src:coin': ['A new coin: true with probability p, independent of all the others.', 'Eine neue Münze: true mit Wahrscheinlichkeit p, unabhängig von allen anderen.'],
    'src:binom': ['A new binomial distribution B(n, p): how many of n coins show true; independent of all the others.', 'Eine neue Binomialverteilung B(n, p): wie viele von n Münzen true zeigen; unabhängig von allen anderen.'],
    'build:not': ['One line in: true where it shows false, and the other way round.', 'Eine Leitung hinein: true, wo sie false zeigt, und umgekehrt.'],
    'build:and': ['Two or more lines in: true when all of them show true.', 'Zwei oder mehr Leitungen hinein: true, wenn alle true zeigen.'],
    'build:or': ['Two or more lines in: true when at least one shows true.', 'Zwei oder mehr Leitungen hinein: true, wenn mindestens eine true zeigt.'],
    'build:xor': ['true when an odd number of the lines show true.', 'true, wenn eine ungerade Zahl der Leitungen true zeigt.'],
    'build:toNat': ['From a coin to a number: false is 0, true is 1.', 'Von einer Münze zu einer Zahl: false ist 0, true ist 1.'],
    'build:count': ['Counts how many of its lines show true.', 'Zählt, wie viele seiner Leitungen true zeigen.'],
    'build:add': ['Adds the numbers of its lines.', 'Addiert die Zahlen seiner Leitungen.'],
    'build:pos': ['true when the number is at least 1.', 'true, wenn die Zahl mindestens 1 ist.'],
    'build:max': ['The largest of the numbers of its lines.', 'Die größte der Zahlen seiner Leitungen.'],
    'walk:north': ['One step up.', 'Ein Schritt nach oben.'], 'walk:south': ['One step down.', 'Ein Schritt nach unten.'],
    'walk:east': ['One step to the right.', 'Ein Schritt nach rechts.'], 'walk:west': ['One step to the left.', 'Ein Schritt nach links.'],
    'walk:step': ['All four ways at once: in Set the figure is wherever it can be.', 'Alle vier Richtungen zugleich: In Set ist die Figur überall, wo sie sein kann.'],
  }
  // A picture of a map Bool → …: the two sides on top, arrows to their images below.
  function mapPicture(f, to = 'bool') {
    const from = ['false', 'true'], imgs = axis(to, from.map(f)), W2 = 150, x = (ks, k) => W2 / 2 + (ks.indexOf(k) - (ks.length - 1) / 2) * 62
    const g = svg('svg', { viewBox: `0 0 ${W2} 74`, class: 'pg-map-picture', width: W2 })
    const defs = svg('defs'), mk = svg('marker', { id: 'pg-map-head', viewBox: '0 0 10 10', refX: 9, refY: 5, markerWidth: 6, markerHeight: 6, orient: 'auto-start-reverse' })
    mk.append(svg('path', { d: 'M0,0 L10,5 L0,10 z', class: 'pg-arrowhead' })); defs.append(mk); g.append(defs)
    for (const k of from) {
      g.append(svg('text', { x: x(from, k), y: 14, 'text-anchor': 'middle', class: 'pg-map-point' }, k))
      g.append(svg('line', { x1: x(from, k), y1: 20, x2: x(imgs, f(k)), y2: 52, class: 'pg-arrow', 'marker-end': 'url(#pg-map-head)' }))
    }
    for (const k of imgs) g.append(svg('text', { x: x(imgs, k), y: 68, 'text-anchor': 'middle', class: 'pg-map-point' }, k))
    return g
  }
  // the moves and building blocks a level offers: [key, label, picture]
  function movesOf(level) {
    const r = level.root
    if (level instanceof Builder) return [
      ...level.sources.filter(x => x.max !== 0).map(x => [/^binom/.test(x.spec) ? 'src:binom' : 'src:' + x.spec, source(x.spec).label(), null]),
      ...level.funs.map(f => ['build:' + f, funLabel(f), el('div', 'pg-map-sym', FUNS[f].sym)])]
    if (level instanceof Grid) return level.moves.map(m => ['walk:' + m, tr(LABEL0[m]), null])
    if (level instanceof Bools) return level.moves.map(m => ['bool:' + m, tr(MOVESB[m].label), mapPicture(k => String(MOVESB[m].f(k === 'true')))])
    return r.dataset.moves.split(',').map(x => x.trim()).filter(Boolean).map(spec => {
      const m = parseMove(spec)
      return ['level:' + spec.split(/\s+/)[0], m.label(), mapPicture(m.f, m.to)]
    })
  }
  const moveCard = ([key, label, pic]) => {
    const card = el('div', 'pg-tip-move'), doc = MOVE_DOC[key]
    if (pic) card.append(pic)
    const t = el('div', 'pg-tip-move-text')
    t.append(el('b', '', label), el('div', '', doc ? doc[LANG === 'de' ? 1 : 0] : ''))
    card.append(t)
    return card
  }
  const itemCard = it => {
    const card = el('div', 'pg-tip-item')
    card.append(el('code', 'pg-inv-sig', it.sig ?? it.name), el('div', '', LANG === 'de' ? it.de ?? '' : it.en ?? ''))
    return card
  }
  // A tip in a box over the stage: a head with ✕ and a foot with "Got it" always in view; the text
  // between them scrolls. It closes with ✕, "Got it", a tap beside it, or Escape.
  function tipBox(head, nodes, done = () => {}) {
    if (document.querySelector('.pg-tip-overlay')) return
    const overlay = el('div', 'pg-tip-overlay'), card = el('div', 'pg-tip-card')
    const top = el('div', 'pg-tip-top'), x = el('button', 'pg-tip-x', '✕'), body = el('div', 'pg-tip-body'), ok = el('button', 'pg-tip-ok', tr('Got it'))
    x.type = ok.type = 'button'; x.setAttribute('aria-label', tr('Close'))
    const close = () => { done(); overlay.remove(); document.removeEventListener('keydown', esc) }
    const esc = ev => { if (ev.key === 'Escape') close() }
    x.addEventListener('click', close); ok.addEventListener('click', close)
    overlay.addEventListener('click', ev => { if (ev.target === overlay) close() })
    document.addEventListener('keydown', esc)
    top.append(el('div', 'pg-tip-head', '💡 ' + head), x)
    body.append(...nodes)
    card.append(top, body, ok)
    overlay.append(card)
    document.body.append(overlay)
    ok.focus({ preventScroll: true })
  }
  // a button of the tool bar: a word on large screens, a symbol over a short word on phones
  function barButton(cls, icon, label, short = label) {
    const b = el('button', `pg-button ${cls}`)
    b.type = 'button'; b.title = label
    b.append(el('span', 'pg-ico', icon), el('span', 'pg-lbl', label), el('span', 'pg-short', short))
    return b
  }
  // The parts of a board, on the stage: the moves (or building blocks) in a column of their own, the
  // rest beside them; Undo and Start over go to the tool bar, what Lean says to the Lean panel.
  function showBoard(level, parts) {
    // drawn anew after each tap: where the board and its parts were scrolled to stays (no jump)
    const scrolled = [level.board, ...level.board.querySelectorAll('.pg-main, .pg-site, .pg-palette')]
      .map(e => [e === level.board ? null : e.classList[0], e.scrollTop, e.scrollLeft])
    const y = window.scrollY
    const keep = () => {
      for (const [c, t, l] of scrolled) { const e = c ? level.board.querySelector('.' + c) : level.board; if (e) { e.scrollTop = t; e.scrollLeft = l } }
      if (window.scrollY !== y) window.scrollTo(window.scrollX, y)
    }
    if (!STAGE) { level.board.replaceChildren(...parts); keep(); return }
    const lean = [], main = [], palette = []
    for (const p of parts) {
      const c = p.classList
      if (c?.contains('pg-lean-state') || (p.tagName === 'PRE' && c?.contains('pg-lean'))) lean.push(p)
      else if (c?.contains('pg-moves-head') || c?.contains('pg-moves') || c?.contains('pg-blocks')) palette.push(p)
      else if (c?.contains('pg-tools')) { p.querySelectorAll('.pg-tool').forEach(b => b.remove()); if (p.children.length) palette.push(p) }
      else main.push(p)
    }
    const m = el('div', 'pg-main'), pal = el('div', 'pg-palette')
    m.append(...main); pal.append(...palette)
    level.board.replaceChildren(m, pal)
    keep()
    level.leanParts = lean
    level.onRendered?.()
  }

  function stage() {
    const roots = [...document.querySelectorAll('.pg-level')]
    if (!roots.length) return
    STAGE = true
    const levels = roots.map((r, i) => new (r.classList.contains('pg-build') ? Builder : r.classList.contains('pg-walk') ? Grid : r.classList.contains('pg-bool') ? Bools : Level)(r, i, () => refresh()))
    levels.forEach(l => { if (l.root.dataset.proof && !SHOW) l.proof = new Proof(l, () => refresh()) })
    const done = l => l.solved && (!l.proof || l.proof.proved)

    // the stage, in place of the heading, the text of the world and the levels
    const stg = el('div', 'pg-stage'), top = el('div', 'pg-stage-top'), titles = el('div', 'pg-stage-titles'), dots = el('div', 'pg-dots')
    const h1 = roots[0].parentElement?.querySelector('h1')
    const worldTitle = el('div', 'pg-stage-title', (h1?.textContent ?? '').replace('🔗', '').trim()), levelTitle = el('div', 'pg-level-title')
    titles.append(worldTitle, levelTitle)
    top.append(titles, dots)
    roots[0].before(stg)
    // the text of the world: between the heading and the first level
    const intro = []
    for (let n = stg.previousSibling; n && n !== h1; n = n.previousSibling) intro.unshift(n)
    const world = el('div', 'pg-world-text'); world.append(...intro); world.hidden = true
    const leanBox = el('div', 'pg-lean-box'), status = el('div', 'pg-status'), bar = el('div', 'pg-toolbar')
    stg.append(top, ...roots, leanBox, status, bar, world)
    if (h1) h1.hidden = true
    document.documentElement.classList.add('pg-playing')

    let current = 0
    const view = () => (levels[current].proof && roots[current].classList.contains('pg-view-proof') ? 'proof' : 'board')
    const setView = v => {
      const l = levels[current]
      roots.forEach(r => r.classList.remove('pg-view-proof'))
      if (v === 'proof' && l.proof) { roots[current].classList.add('pg-view-proof'); l.proof.update(); showProofTip(current) }
      refresh()
      if (v === 'proof' && !document.querySelector('.pg-tip-overlay')) setTimeout(() => l.proof?.input?.focus({ preventScroll: true }), 50)
    }
    // the name of a level: the words in italics at the start of its text
    const levelName = k => {
      const t = [...roots[k].querySelectorAll(':scope > .pg-text > .pg-lang:not(.pg-proof-text)')].find(e => e.lang === LANG)
      const em = t?.querySelector('p > :is(em, strong):first-child')
      return em ? em.textContent.trim().replace(/[.:]$/, '') : ''
    }
    const clone = nodes => nodes.map(n => n.cloneNode(true))
    const levelText = k => clone([...roots[k].querySelectorAll(':scope > .pg-text > .pg-lang:not(.pg-proof-text)')])
    const worldText = () => clone([...world.childNodes])
    // the moves new in a level: not offered by a level before it on this page
    const newMoves = k => {
      const before = new Set(levels.slice(0, k).flatMap(l => movesOf(l).map(m => m[0])))
      const seen = new Set()
      return movesOf(levels[k]).filter(m => !before.has(m[0]) && !seen.has(m[0]) && seen.add(m[0]))
    }
    const newItems = k => { const p = levels[k].proof; return p ? INVENTORY.filter(i => p.since(i) === p.no && i.kind !== 'lemma') : [] }
    const boardTip = (k, withWorld) => {
      const moves = newMoves(k)
      return [...levelText(k), ...(moves.length ? [el('div', 'pg-tip-sub', tr('New in this level')), ...moves.map(moveCard)] : []),
        ...(withWorld && world.childNodes.length ? [el('div', 'pg-tip-sub', tr('This world')), ...worldText()] : [])]
    }
    const proofTip = k => {
      const items = newItems(k)
      return [...clone(levels[k].proof?.texts ?? []), ...(items.length ? [el('div', 'pg-tip-sub', tr('New in this proof')), ...items.map(itemCard)] : [])]
    }
    const tipsOff = () => { try { return localStorage.getItem('pg:tips') === 'off' } catch { return false } }
    const once = (key, f) => {
      if (tipsOff()) return
      try { if (localStorage.getItem(key)) return } catch {}
      f(() => { try { localStorage.setItem(key, '1') } catch {} })
    }
    const showBoardTip = k => once(`${levels[k].key}:tip`, mark => tipBox(tr('Tip'), boardTip(k, k === 0), mark))
    const showProofTip = k => once(`${levels[k].key}:proof-tip`, mark => tipBox(tr('Tip'), proofTip(k), mark))

    // the tool bar
    const undo = barButton('pg-undo', '↶', tr('Undo')), restart = barButton('pg-restart', '⟲', tr('Start over'), tr('Restart'))
    const lean = barButton('pg-lean-button', 'λ', 'Lean'), tips = barButton('pg-tips-button', '💡', tr('Tips'))
    const toggle = barButton('pg-view-button', '∀', tr('Proof ')), next = barButton('pg-next-button', '›', tr('Next ›'), tr('Next'))
    const nextWorld = document.querySelector('nav.prev-next-buttons a[rel="next"]')
    undo.addEventListener('click', () => { const l = levels[current]; if (view() === 'proof') l.proof.back(); else l.undo() })
    restart.addEventListener('click', () => { const l = levels[current]; if (view() === 'proof') l.proof.restart(); else l.reset() })
    let leanOpen = false
    try { leanOpen = localStorage.getItem('pg:lean') === '1' } catch {}
    lean.addEventListener('click', () => { leanOpen = !leanOpen; try { localStorage.setItem('pg:lean', leanOpen ? '1' : '0') } catch {}; refresh() })
    tips.addEventListener('click', () => tipBox(tr('Tips'), view() === 'proof' ? proofTip(current) : boardTip(current, true)))
    toggle.addEventListener('click', () => setView(view() === 'proof' ? 'board' : 'proof'))
    next.addEventListener('click', () => {
      if (current < levels.length - 1) show(current + 1)
      else if (nextWorld) location.href = nextWorld.getAttribute('href').replace(/#.*$/, '')
    })
    bar.append(undo, restart, ...(SHOW ? [] : [lean]), tips, ...(SHOW ? [] : [toggle]), next)

    const refresh = () => {
      const l = levels[current], v = view()
      dots.replaceChildren(...levels.map((x, k) => {
        const d = el('button', 'pg-dot' + (done(x) ? ' pg-dot-done' : x.solved ? ' pg-dot-half' : '') + (k === current ? ' pg-dot-current' : ''))
        d.type = 'button'
        d.title = tr('Level {i} of {n}', { i: k + 1, n: levels.length })
        d.addEventListener('click', () => show(k))
        return d
      }))
      levels.forEach(x => x.proof?.update())
      levelTitle.textContent = levelName(current)
      status.textContent = (v === 'proof' ? l.proof.status() : l.status?.()) ?? ''
      status.classList.toggle('pg-status-done', v === 'proof' ? !!l.proof.done : !!l.solved && /^✓/.test(status.textContent))
      undo.disabled = restart.disabled = v === 'proof' ? !l.proof.canUndo : !l.canUndo
      lean.hidden = v === 'proof'
      lean.setAttribute('aria-pressed', String(leanOpen))
      leanBox.hidden = !leanOpen || v === 'proof' || !l.leanParts?.length
      if (!leanBox.hidden) leanBox.replaceChildren(...l.leanParts)
      toggle.hidden = !l.proof
      toggle.disabled = !l.solved
      toggle.title = l.solved ? '' : tr('Solve the board first.')
      for (const e of toggle.querySelectorAll('.pg-lbl, .pg-short')) e.textContent = tr(v === 'proof' ? 'Board' : 'Proof ')
      toggle.querySelector('.pg-ico').textContent = v === 'proof' ? '▦' : '∀'
      const last = current === levels.length - 1
      next.disabled = last && !nextWorld
      for (const e of next.querySelectorAll('.pg-lbl')) e.textContent = tr(last ? 'Next world ›' : 'Next ›')
      next.classList.toggle('pg-glow', done(l) && !next.disabled)
      const n = levels.filter(done).length
      if (n !== doneBefore) { doneBefore = n; worldMap() }
    }
    let doneBefore = -1
    levels.forEach(l => { l.onRendered = () => { if (l === levels[current]) refresh() } })
    const show = k => {
      current = Math.max(0, Math.min(levels.length - 1, k))
      roots.forEach((r, i) => { r.hidden = i !== current; r.classList.remove('pg-view-proof') })
      history.replaceState(null, '', `${location.pathname}${location.search}#level-${current + 1}`)
      try { localStorage.setItem(`pg:last:${siteRoot()}`, JSON.stringify({ href: `${location.pathname}#level-${current + 1}`, title: `${worldTitle.textContent} · ${levelName(current) || current + 1}` })) } catch {}
      levels[current].render()
      refresh()
      showBoardTip(current)
    }
    levels.forEach((l, k) => {
      l.onNextLevel = () => show(k + 1)
      l.onNext = () => (l.proof ? setView('proof') : current < levels.length - 1 ? show(k + 1) : next.click())
    })
    // ← and → go to the previous and next level (not while typing)
    document.addEventListener('keydown', ev => {
      if (ev.target.closest?.('input, textarea') || ev.altKey || ev.ctrlKey || ev.metaKey || document.querySelector('.pg-tip-overlay')) return
      if (ev.key === 'ArrowLeft') show(current - 1)
      if (ev.key === 'ArrowRight') show(current + 1)
    })
    try { localStorage.setItem(levelsKey(location.pathname), JSON.stringify(levels.map(l => !!l.proof))) } catch {}
    const fromHash = Number(/^#level-(\d+)$/.exec(location.hash)?.[1] ?? 0) - 1
    show(fromHash >= 0 ? fromHash : Math.max(0, levels.findIndex(l => !done(l))))
    // The stage fills the screen below the header; measured again when the window changes, without
    // scrolling (on phones the window changes when the address bar comes or goes, while one plays).
    let resizing
    const fit = () => {
      const top = stg.getBoundingClientRect().top + window.scrollY
      stg.style.height = `${Math.max(360, window.innerHeight - top - 8)}px`
    }
    window.scrollTo(0, 0)
    fit()
    window.addEventListener('resize', () => { clearTimeout(resizing); resizing = setTimeout(fit, 120) })
  }

  // ---------------------------------------------------------------- the map of the worlds

  // In place of the table of contents: a circle per world, one below the other, with the share of
  // its levels done (board solved, and proof proved where there is one), and lines along the way.
  // How many levels a world has, and which have a proof, is kept when its page is shown, and
  // fetched from its page once otherwise.
  Object.assign(DE, { Worlds: 'Welten', 'Lexicon': 'Lexikon', '📖 Lexicon': '📖 Lexikon', '▶ Start': '▶ Start', '▶ Continue': '▶ Weiterspielen',
    'or start from the beginning': 'oder von vorn beginnen', 'Continue: {w}': 'Weiter: {w}' })
  const siteRoot = () => new URL('.', document.baseURI).pathname
  const worldLinks = () => [...document.querySelectorAll('#toc .split-toc.book tr')].map(tr => {
    const a = tr.querySelector('a'); if (!a) return null
    return { a, num: tr.querySelector('.num')?.textContent.trim().replace(/\.$/, '') ?? '', path: new URL(a.href).pathname }
  }).filter(w => w && !/\/Lexicon\/$/.test(w.path))
  const levelsKey = path => `pg:levels:${path}`
  const fetched = new Set()
  function worldMap() {
    const toc = document.querySelector('#toc'), worlds = worldLinks()
    if (!toc || !worlds.length) return
    const info = w => { try { return JSON.parse(localStorage.getItem(levelsKey(w.path))) } catch { return null } }
    for (const w of worlds) if (!info(w) && !fetched.has(w.path)) {
      fetched.add(w.path)
      fetch(w.a.href.replace(/#.*$/, '')).then(r => r.text()).then(html => {
        const doc = new DOMParser().parseFromString(html, 'text/html')
        const levels = [...doc.querySelectorAll('.pg-level')].filter(ours).map(r => !!r.dataset.proof)
        try { localStorage.setItem(levelsKey(w.path), JSON.stringify(levels)) } catch {}
        worldMap()
      }).catch(() => {})
    }
    const ls = k => { try { return localStorage.getItem(k) } catch { return null } }
    const count = w => {
      const levels = info(w)
      if (!levels) return null
      return [levels.filter((proof, i) => ls(`pg:${w.path}:${i}`) === '1' && (SHOW || !proof || ls(`pg:${w.path}:${i}:proofd`) === '1')).length, levels.length]
    }
    const W2 = 250, dy = 56, x = 30, y0 = 26, H = y0 + (worlds.length - 1) * dy + 30
    const map = svg('svg', { viewBox: `0 0 ${W2} ${H}`, class: 'pg-map' })
    for (let i = 1; i < worlds.length; i++) map.append(svg('line', { x1: x, y1: y0 + (i - 1) * dy, x2: x, y2: y0 + i * dy, class: 'pg-map-edge' }))
    worlds.forEach((w, i) => {
      const y = y0 + i * dy, r = 18, c = count(w), frac = c && c[1] ? c[0] / c[1] : 0
      const name = w.a.textContent.trim()
      const g = svg('a', { href: w.a.getAttribute('href').replace(/#.*$/, ''), class: 'pg-map-world' + (w.path === location.pathname ? ' pg-map-here' : '') + (c && c[0] === c[1] && c[1] ? ' pg-map-done' : '') })
      g.append(svg('title', {}, c ? `${name}: ${c[0]}/${c[1]}` : name))
      g.append(svg('circle', { cx: x, cy: y, r, class: 'pg-map-disc' }))
      if (frac > 0 && frac < 1) {
        const t = 2 * Math.PI * frac, ex = x + r * Math.sin(t), ey = y - r * Math.cos(t)
        g.append(svg('path', { d: `M${x},${y - r} A${r},${r} 0 ${frac > 0.5 ? 1 : 0} 1 ${ex},${ey}`, class: 'pg-map-ring' }))
      }
      // (the worlds before chance have no number: a sign of their own)
      const sign = /True-and-False\/$/.test(w.path) ? '⊤' : /Walking-on-the-Grid\/$/.test(w.path) ? '⌗' : '•'
      g.append(svg('text', { x, y: y + 6, 'text-anchor': 'middle', class: 'pg-map-n' }, w.num || sign))
      g.append(svg('text', { x: x + r + 8, y: y - 1, class: 'pg-map-name' }, name))
      g.append(svg('text', { x: x + r + 8, y: y + 13, class: 'pg-map-count' }, c ? `${c[0]}/${c[1]}` : ''))
      map.append(g)
    })
    toc.querySelector('.pg-worlds')?.remove()
    const box = el('div', 'pg-worlds')
    box.append(el('div', 'pg-worlds-title', tr('Worlds')), map)
    const lex = [...document.querySelectorAll('#toc a')].find(a => /\/Lexicon\/$/.test(new URL(a.href).pathname))
    if (lex) {
      const t = el('a', 'pg-map-lexicon' + (new URL(lex.href).pathname === location.pathname ? ' pg-map-here' : ''), tr('📖 Lexicon'))
      t.href = lex.getAttribute('href').replace(/#.*$/, '')
      box.append(t)
    }
    ;(toc.querySelector('.first') ?? toc).prepend(box)
    toc.classList.add('pg-has-map')
  }

  // The front page: one button, which starts at the first world or goes on where one left off.
  function startButton() {
    if (document.querySelector('.pg-level, .pg-lexicon')) return
    const first = worldLinks()[0], h1 = document.querySelector('main h1')
    if (!first || !h1) return
    let last = null
    try { last = JSON.parse(localStorage.getItem(`pg:last:${siteRoot()}`)) } catch {}
    const box = el('div', 'pg-start')
    const go = el('a', 'pg-start-button', last ? tr('▶ Continue') : tr('▶ Start'))
    go.href = last?.href ?? first.a.getAttribute('href').replace(/#.*$/, '')
    box.append(go)
    if (last) {
      box.append(el('div', 'pg-start-where', tr('Continue: {w}', { w: last.title })))
      const again = el('a', 'pg-start-again', tr('or start from the beginning'))
      again.href = first.a.getAttribute('href').replace(/#.*$/, '')
      box.append(again)
    }
    h1.after(box)
    document.documentElement.classList.add('pg-front')
  }

  // ---------------------------------------------------------------- the lexicon

  // Every move and building block (with its picture), and every tactic and rule, of the worlds of
  // this edition; the same texts as in the tips.
  Object.assign(DE, {
    'Moves and building blocks': 'Züge und Bausteine', 'Moves on a coin': 'Züge auf einer Münze', 'Building blocks of the circuits': 'Bausteine der Schaltpläne',
    'Moves of a sure coin': 'Züge einer sicheren Münze', 'Moves on the grid': 'Züge auf dem Gitter', 'Tactics and rules': 'Taktiken und Regeln',
    'Rules': 'Regeln', 'Your lemmas': 'Deine Lemmas',
  })
  function lexicon() {
    const box = document.querySelector('.pg-lexicon')
    if (!box) return
    const has = slug => [...document.querySelectorAll('#toc a')].some(a => new URL(a.href).pathname.endsWith(`/${slug}/`))
    const bool = has('True-and-False'), walk = has('Walking-on-the-Grid'), coin = has('One-Coin')
    const parts = [el('h2', '', tr('Moves and building blocks'))]
    const group = (title, cards) => { if (cards.length) parts.push(el('h3', '', title), ...cards.map(moveCard)) }
    if (bool) group(tr('Moves of a sure coin'), Object.keys(MOVESB).map(m => ['bool:' + m, tr(MOVESB[m].label), mapPicture(k => String(MOVESB[m].f(k === 'true')))]))
    if (walk) group(tr('Moves on the grid'), Object.keys(LABEL0).map(m => ['walk:' + m, tr(LABEL0[m]), null]))
    if (coin) group(tr('Moves on a coin'), ['id', 'not', 'heads', 'tails', 'toNat', 'payoff 5 -2'].map(spec => {
      const m = parseMove(spec); return ['level:' + spec.split(' ')[0], m.label(), mapPicture(m.f, m.to)]
    }))
    if (coin) group(tr('Building blocks of the circuits'), [['src:coin', source('coin').label(), null], ['src:binom', 'B(n, p)', null],
      ...Object.keys(FUNS).map(f => ['build:' + f, funLabel(f), el('div', 'pg-map-sym', FUNS[f].sym)])])
    if (!SHOW) {
      parts.push(el('h2', '', tr('Tactics and rules')))
      const shown = INVENTORY.filter(i => (i.at && coin) || (i.wb && bool) || (i.w0 && walk))
      for (const [kind, title] of [['tactic', tr('Tactics')], ['rule', tr('Rules')], ['lemma', tr('Your lemmas')]]) {
        const items = shown.filter(i => i.kind === kind)
        if (!items.length) continue
        parts.push(el('h3', '', title))
        for (const it of items) {
          const card = el('div', 'pg-tip-item')
          const text = LANG === 'de' ? it.de ?? it.deb ?? it.de0 : it.en ?? it.enb ?? it.en0
          card.append(el('b', '', it.name + ' '), el('code', 'pg-inv-sig', it.sig ?? it.sig0 ?? ''), el('div', '', text ?? ''))
          parts.push(card)
        }
      }
    }
    box.replaceChildren(...parts)
  }

  function init() {
    SHOW = document.querySelector('meta[name="pg-edition"]')?.content === 'show'
    if (SHOW) BACKEND = null
    // the parts of other editions go, those of this one stay (`:::::only`, ProbGame/Level.lean)
    document.querySelectorAll('.pg-only').forEach(d => { if (ours(d)) d.replaceWith(...d.childNodes); else d.remove() })
    applyLang()
    translatePage()
    languageSwitch()
    stage()
    lexicon()
    startButton()
    worldMap()
  }
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init)
  else init()
})()
