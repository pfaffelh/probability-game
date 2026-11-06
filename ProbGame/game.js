// The probability game: distributions as sand, moves as maps, the result as the image measure.
//
// Each `.pg-level` (from `::::level` in ProbGame/Level.lean) has a start distribution, a target and
// the moves offered. A distribution is a space ('bool', 'nat', 'int') with masses on its points that
// are polynomials in p (with exact fractions: the same for every p); the picture draws them for an example p,
// which a slider changes; a move is a map, and applying it pushes the distribution forward: the sand of each
// point flows to its image (animated), where it piles up with the sand of the other points of the
// same image. A tapped column shows its preimage. The level is solved when the distribution is the
// target; its Lean statement (for every p) is then shown. A world page shows one level at a time,
// with a dot per level above it; progress is kept in the browser.
(function () {
  'use strict'

  // ---------------------------------------------------------------- language

  let LANG = 'en'
  try { LANG = localStorage.getItem('pg:lang') ?? ((navigator.language ?? '').startsWith('de') ? 'de' : 'en') } catch {}
  const DE = {
    Moves: 'Züge', Undo: 'Zurück', 'Start over': 'Neu anfangen', 'Next level ›': 'Nächstes Level ›',
    'Solved!': 'Geschafft!', Target: 'Ziel', 'In Lean, for every p:': 'In Lean, für jedes p:', 'proved': 'bewiesen',
    'Tap a column to see where its sand came from.': 'Tippe eine Säule an, um zu sehen, woher ihr Sand kommt.',
    'This move needs a coin, not a number.': 'Dieser Zug braucht eine Münze, keine Zahl.',
    'Level {i} of {n}': 'Level {i} von {n}', 'nothing flows here': 'hierher fließt nichts',
    '{b}: the sand comes from {from}, P = {sum}{m}': '{b}: Der Sand kommt aus {from}, P = {sum}{m}',
    'not: swap the sides': 'not: Seiten tauschen', 'always true': 'immer true', 'always false': 'immer false', 'do nothing': 'nichts tun',
    'toNat: false = 0, true = 1': 'toNat: false = 0, true = 1', 'true: win {a}, false: {b}': 'true: {a} gewinnen, false: {b}',
    'the start': 'der Anfang', 'Lean:': 'Lean:',
    'confirmed by Lean, for every p': 'von Lean bestätigt, für jedes p', 'Lean is normalising …': 'Lean normalisiert …',
    'Lean disagrees: the target is': 'Lean widerspricht: Das Ziel ist',
    'Lean is not connected: the board checks for every p by itself, without Lean.': 'Lean ist nicht verbunden: Das Spielfeld prüft selbst, für jedes p, aber ohne Lean.',
    'Task: bring the sand into the shape of the target:': 'Aufgabe: Bring den Sand in die Form des Ziels:',
    'surely {b}': 'sicher {b}', 'the picture for p =': 'das Bild für p =', '(only an example; the masses hold for every p)': '(nur ein Beispiel; die Massen gelten für jedes p)',
  }
  const tr = (s, vars = {}) => (LANG === 'de' ? DE[s] ?? s : s).replace(/\{(\w+)\}/g, (_, k) => vars[k])
  const applyLang = () => {
    document.documentElement.classList.toggle('pg-de', LANG === 'de')
    document.documentElement.lang = LANG
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
  const BACKEND = (() => {
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
  const normalise = (context, expr) => {
    if (!BACKEND) return Promise.resolve({ error: { message: 'no backend' } })
    if (!normalForms.has(expr))
      normalForms.set(expr, fetch(BACKEND.replace(/\/$/, '') + '/simp', { method: 'POST', headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ context, open: 'MeasureTheory DiscreteMeasure unitInterval', vars: '(p : unitInterval)', rules: RULES, expr }) })
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
      case 'id': return { from: 'bool', to: 'bool', f: k => k, lean: 'id', label: () => tr('do nothing') }
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
  // the image measure: the mass of each point flows to its image
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

    // solved: the sand is the target, and Lean agrees (if it is connected)
    get done() { return sameDist(this.dist, this.target) && this.leanAgrees() !== false && (!BACKEND || !this.leanTarget || this.leanAgrees() === true) }

    check() {
      if (this.animating || !this.done) return
      const first = !this.solved
      try { localStorage.setItem(this.key, '1') } catch {}
      this.render()
      this.onSolved?.(first)
    }

    flash(text) { this.info.textContent = text; this.info.classList.add('pg-warn'); setTimeout(() => this.info.classList.remove('pg-warn'), 1200) }

    // The sand of each point flows to its image, piling up there (900 ms).
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
        const r = svg('rect', { class: 'pg-sand', x: xa[k] - BAR / 2, y: y0, width: BAR, height: h, rx: 3 })
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
        if (hh > 0) g.append(svg('rect', { class: 'pg-target-sand', x: x - bw / 2, y: base - hh, width: bw, height: hh, rx: 3 }))
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
        if (h > 0) bar.append(svg('rect', { class: 'pg-sand', x: xs[k] - BAR / 2, y: BASE - h, width: BAR, height: h, rx: 3 }))
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

      // what a tapped column is made of: its preimage under the last move
      this.info = el('div', 'pg-info')
      if (this.picked !== null) {
        const m = d.mass.get(this.picked) ?? ZERO, name = pointName(d.space, this.picked)
        const last = this.steps[this.steps.length - 1]
        if (last) {
          const pre = axis(last.before.space, [...last.before.mass.keys()]).filter(k => last.before.mass.has(k) && last.move.f(k) === this.picked)
          const from = `{${pre.map(k => pointName(last.before.space, k)).join(', ')}}`
          const sum = pre.length > 1 ? `${pre.map(k => { const q = last.before.mass.get(k); return paren(q) }).join(' + ')} = ` : ''
          this.info.textContent = pre.length ? tr('{b}: the sand comes from {from}, P = {sum}{m}', { b: name, from, sum, m: m.toString() })
            : `${name}: ${tr('nothing flows here')}`
        } else this.info.textContent = `${name}: P = ${m} (${tr('the start')})`
      } else this.info.textContent = tr('Tap a column to see where its sand came from.')

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
      task.append(el('b', '', tr('Task: bring the sand into the shape of the target:') + ' '),
        tk.length === 1 && (this.target.mass.get(tk[0]) ?? ZERO).eq(ONE) ? tr('surely {b}', { b: pointName(this.target.space, tk[0]) })
          : tk.map(k => `P(${pointName(this.target.space, k)}) = ${this.target.mass.get(k)}`).join(', '))
      const row = el('div', 'pg-row')
      row.append(s, this.targetPicture())
      // the example p of the picture
      const slider = el('label', 'pg-slider')
      const input = el('input'); input.type = 'range'; input.min = '0.05'; input.max = '0.95'; input.step = '0.05'; input.value = String(P)
      input.addEventListener('input', () => { P = Number(input.value); try { localStorage.setItem('pg:p', input.value) } catch {}; this.render() })
      slider.append(`${tr('the picture for p =')} ${P.toFixed(2)} `, input, el('span', 'pg-slider-note', ' ' + tr('(only an example; the masses hold for every p)')))
      const parts = [task, row, slider, this.info, ln, el('div', 'pg-moves-head', tr('Moves')), moves, tools, lean]
      if (done) {
        const box = el('div', 'pg-solved')
        box.append(el('div', 'pg-solved-head', '✓ ' + tr('Solved!') + (this.leanAgrees() ? ` (${tr('confirmed by Lean, for every p')})` : '')))
        // what Lean has confirmed: the moves played are the target, for every p (or, without Lean, the
        // statement of the level, proved in Proofs/)
        const statement = this.leanAgrees() ? `${functorForm(this.leanState())} = ${functorForm(this.leanGoal.result)}` : this.leanStatement
        if (statement) {
          box.append(el('div', 'pg-solved-lean-head', tr('In Lean, for every p:')))
          box.append(el('pre', 'pg-lean', statement))
        }
        const next = el('button', 'pg-next', tr(this.root.dataset.proof ? 'To the proof ↓' : 'Next level ›'))
        next.type = 'button'
        next.addEventListener('click', () => this.onNext?.())
        box.append(next)
        parts.push(box)
      }
      this.board.replaceChildren(...parts)
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
    'number of true': 'Anzahl true', 'at least 1': 'mindestens 1', maximum: 'Maximum', 'new p-coin': 'neue p-Münze', Check: 'Prüfen', 'Remove the last': 'Letztes entfernen',
    '{n} left': 'noch {n}', 'Building blocks': 'Bausteine',
    'Lay down a coin with “new p-coin”. Tap lines to choose them (in this order), then a function.': 'Leg mit „neue p-Münze“ eine Münze hin. Tippe Leitungen an, um sie auszuwählen (in dieser Reihenfolge), dann eine Funktion.',
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
    if (spec === 'coin') return { space: 'bool', prefix: 'M', lean: 'coin p', label: () => tr('new p-coin'),
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
      this.nodes = []      // { src } (a source) or { fun, inputs: [indices] }
      try { this.nodes = JSON.parse(localStorage.getItem(this.key + ':tree') ?? '[]').map(n => (n.coin ? { src: 'coin' } : n)) } catch {}
      this.selected = []   // indices, in the order chosen
      this.checked = null  // { node, ok }
      this.message = ''
      this.render()
    }

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
      this.nodes.push({ src: src.spec }); this.selected = [this.nodes.length - 1]; this.changed()
    }
    apply(f) {
      const F = FUNS[f], sel = this.selected
      const bad = sel.length < F.arity || (!F.more && sel.length > F.arity) ? tr(F.more ? 'Choose at least {n} lines first (tap them).' : 'Choose {n} lines first (tap them).', { n: F.arity })
        : sel.some(j => this.space(j) !== F.from) ? tr(F.from === 'bool' ? 'This function needs coins (true/false).' : 'This function needs numbers.') : null
      if (bad) { this.message = bad; this.render(); return }
      this.nodes.push({ fun: f, inputs: sel.slice() }); this.selected = [this.nodes.length - 1]; this.changed()
    }
    pick(i) {
      const k = this.selected.indexOf(i)
      if (k >= 0) this.selected.splice(k, 1); else this.selected.push(i)
      this.message = ''; this.render()
    }
    removeLast() { if (!this.nodes.length) return; this.nodes.pop(); this.selected = this.selected.filter(j => j < this.nodes.length); this.changed() }
    reset() { this.nodes = []; this.selected = []; this.changed() }

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
        if (hh > 0) c.append(svg('rect', { class: 'pg-mini-sand', x: xx - bw / 2, y: base - hh, width: bw, height: hh, rx: 2 }))
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
      blocks.append(el('div', 'pg-moves-head', tr('Building blocks')))
      for (const src of this.sources) {
        if (src.max === 0) continue
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
      site.append(this.nodes.length ? this.circuit() : el('div', 'pg-site-empty', tr('Lay down a coin with “new p-coin”. Tap lines to choose them (in this order), then a function.')))
      this.targetBox = el('div', 'pg-target-box' + (done ? ' pg-card-ok' : ''))
      this.targetBox.append(this.targetPicture())
      const area = el('div', 'pg-build-area')
      area.append(site, this.targetBox)

      const tools = el('div', 'pg-tools')
      const check = el('button', 'pg-check', tr('Check')), undo = el('button', 'pg-tool', '↶ ' + tr('Remove the last')), reset = el('button', 'pg-tool', '⟲ ' + tr('Start over'))
      check.type = undo.type = reset.type = 'button'
      undo.disabled = reset.disabled = !this.nodes.length
      check.addEventListener('click', () => this.check())
      undo.addEventListener('click', () => this.removeLast()); reset.addEventListener('click', () => this.reset())
      tools.append(check, undo, reset)

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
        box.append(el('div', 'pg-solved-head', '✓ ' + tr('Solved!')))
        box.append(el('div', 'pg-solved-lean-head', tr('As a do block in Lean:')))
        box.append(el('pre', 'pg-lean', this.lean(this.checked.node)))
        const next = el('button', 'pg-next', tr(this.root.dataset.proof ? 'To the proof ↓' : 'Next level ›'))
        next.type = 'button'
        next.addEventListener('click', () => this.onNext?.())
        box.append(next)
        parts.push(box)
      }
      this.board.replaceChildren(...parts)
    }
  }
  Builder.prototype.targetPicture = Level.prototype.targetPicture

  // ---------------------------------------------------------------- the proof

  // The second part of a level, as in the Natural Number Game: once the board is solved, its statement
  // is to be proved in Lean, one tactic after another (`/start` and `/check` of the bridge, in the
  // context Lean/Rules.lean). The inventory holds the tactics and rules introduced so far (by the
  // number of the level, `"2.3"`) and the lemmas proved in earlier levels; a line that uses anything
  // else is refused before Lean sees it.

  const INVENTORY = [
    { name: 'rw', kind: 'tactic', at: '1.1', insert: 'rw []', sig: 'rw [h]   rw [← h]   rw [h₁, h₂]',
      en: 'Rewrites the goal with the equation h: its left side becomes its right side (with ←, the other way round). Closes the goal when it then reads a = a. It does not rewrite where names bound in a do block occur; there, use simp only.',
      de: 'Schreibt das Ziel mit der Gleichung h um: Ihre linke Seite wird zu ihrer rechten (mit ← umgekehrt). Schließt das Ziel, wenn es danach a = a lautet. Es schreibt nicht dort um, wo in einem do-Block gebundene Namen vorkommen; dort hilft simp only.' },
    { name: 'rfl', kind: 'tactic', at: '1.3', insert: 'rfl', sig: 'rfl',
      en: 'Closes a goal a = b whose sides are the same after computing (!true is false, 1 + 1 is 2).',
      de: 'Schließt ein Ziel a = b, dessen Seiten nach Ausrechnen gleich sind (!true ist false, 1 + 1 ist 2).' },
    { name: 'congr', kind: 'tactic', at: '1.4', insert: 'congr 1', sig: 'congr 1',
      en: 'For a goal f a = f b, or μ >>= g = μ >>= h (a do block): reduces it to the parts that differ (a = b, g = h).',
      de: 'Für ein Ziel f a = f b, oder μ >>= g = μ >>= h (ein do-Block): führt es auf die Teile zurück, die sich unterscheiden (a = b, g = h).' },
    { name: 'funext', kind: 'tactic', at: '1.4', insert: 'funext x', sig: 'funext x',
      en: 'For a goal g = h between functions: it suffices that g x = h x for every x.',
      de: 'Für ein Ziel g = h zwischen Funktionen: Es genügt, dass g x = h x für jedes x.' },
    { name: 'cases', kind: 'tactic', at: '1.4', insert: 'cases x', sig: 'cases x',
      en: 'Splits into the cases of x: for x : Bool, the goals for false and for true, one after the other.',
      de: 'Teilt in die Fälle von x: für x : Bool die Ziele für false und für true, eines nach dem anderen.' },
    { name: 'simp only', kind: 'tactic', at: '2.2', insert: 'simp only []', sig: 'simp only [h₁, h₂, …]',
      en: 'Rewrites with the given rules everywhere, also inside do blocks, as often as it can; closes the goal when both sides become the same.',
      de: 'Schreibt mit den angegebenen Regeln überall um, auch in do-Blöcken, so oft es geht; schließt das Ziel, wenn beide Seiten gleich werden.' },
    { name: '<;>', kind: 'tactic', at: '2.5', insert: ' <;> ', sig: 't₁ <;> t₂',
      en: 'Runs t₂ on every goal that t₁ leaves: cases x <;> cases y <;> rfl.',
      de: 'Führt t₂ auf jedem Ziel aus, das t₁ übrig lässt: cases x <;> cases y <;> rfl.' },
    { name: "induction'", kind: 'tactic', at: '3.3', insert: "induction' n with n ih", sig: "induction' n with n ih",
      en: 'Induction on the natural number n: first the goal for 0, then the goal for n + 1, with the hypothesis ih for n.',
      de: 'Induktion nach der natürlichen Zahl n: zuerst das Ziel für 0, dann das Ziel für n + 1, mit der Annahme ih für n.' },
    { name: 'coin_not', kind: 'rule', at: '1.1', sig: 'not <$> coin p = coin (σ p)', en: 'Flipping a coin swaps the masses.', de: 'Umdrehen tauscht die Massen.' },
    { name: 'coin_const', kind: 'rule', at: '1.2', sig: '(fun _ => b) <$> coin p = pure b', en: 'A constant move: all the sand to one point.', de: 'Ein konstanter Zug: der ganze Sand an einen Punkt.' },
    { name: 'map_pure', kind: 'rule', at: '1.3', sig: 'f <$> pure a = pure (f a)', en: 'A move on a point mass moves the point.', de: 'Ein Zug auf einer Punktmasse verschiebt den Punkt.' },
    { name: 'map_map', kind: 'rule', at: '1.6', sig: 'g <$> (f <$> μ) = (fun x => g (f x)) <$> μ', en: 'Two moves are one move.', de: 'Zwei Züge sind ein Zug.' },
    { name: 'coin_and', kind: 'rule', at: '2.1', sig: '(do let x ← coin p; let y ← coin q; pure (x && y)) = coin (p * q)', en: 'Independence: both true with probability p · q.', de: 'Unabhängigkeit: beide true mit Wahrscheinlichkeit p · q.' },
    { name: 'bind_map_left', kind: 'rule', at: '2.2', sig: '(do let x ← f <$> μ; g x) = (do let x ← μ; g (f x))', en: 'A move on a throw goes into the result.', de: 'Ein Zug auf einem Wurf wandert ins Ergebnis.' },
    { name: 'map_bind', kind: 'rule', at: '2.3', sig: 'f <$> (do let x ← μ; g x) = (do let x ← μ; f <$> g x)', en: 'A move after a do block goes into it.', de: 'Ein Zug nach einem do-Block wandert in ihn hinein.' },
    { name: 'or_eq', kind: 'rule', at: '2.3', sig: '(x || y) = !(!x && !y)', en: 'De Morgan.', de: 'De Morgan.' },
    { name: 'Bool.and_not_self', kind: 'rule', at: '2.4', sig: '(x && !x) = false', en: 'Never both x and not x.', de: 'Nie zugleich x und nicht x.' },
    { name: 'coin_unused', kind: 'rule', at: '2.4', sig: '(do let _ ← coin p; ν) = ν', en: 'A coin whose result is not used changes nothing.', de: 'Eine Münze, deren Ergebnis nicht benutzt wird, ändert nichts.' },
    { name: 'binom_zero', kind: 'rule', at: '2.6', sig: 'binom p 0 = pure 0', en: 'The definition of binom: no throw.', de: 'Die Definition von binom: kein Wurf.' },
    { name: 'binom_succ', kind: 'rule', at: '2.6', sig: 'binom p (n + 1) = do let X ← coin p; let Y ← binom p n; pure (X.toNat + Y)', en: 'The definition of binom: one throw more.', de: 'Die Definition von binom: ein Wurf mehr.' },
    { name: 'bind_assoc', kind: 'rule', at: '2.6', sig: '(do let y ← (do let x ← μ; f x); g y) = (do let x ← μ; let y ← f x; g y)', en: 'A do block in a do block is one do block.', de: 'Ein do-Block in einem do-Block ist ein do-Block.' },
    { name: 'pure_bind', kind: 'rule', at: '2.6', sig: '(do let x ← pure a; f x) = f a', en: 'Throwing a point mass is no throw.', de: 'Eine Punktmasse zu werfen ist kein Wurf.' },
    { name: 'add_zero', kind: 'rule', at: '2.6', sig: 'n + 0 = n', en: 'Adding zero.', de: 'Null addieren.' },
    { name: 'add_assoc', kind: 'rule', at: '3.1', sig: 'a + b + c = a + (b + c)', en: 'Brackets in sums.', de: 'Klammern in Summen.' },
    { name: 'map_eq_pure_bind', kind: 'rule', at: '3.2', sig: 'f <$> μ = do let x ← μ; pure (f x)', en: 'A move as a do block.', de: 'Ein Zug als do-Block.' },
    { name: 'zero_add', kind: 'rule', at: '3.3', sig: '0 + n = n', en: 'Adding to zero.', de: 'Zu null addieren.' },
    { name: 'bind_pure', kind: 'rule', at: '3.5', sig: '(do let x ← μ; pure x) = μ', en: 'A throw whose result is the result.', de: 'Ein Wurf, dessen Ergebnis das Ergebnis ist.' },
    { name: 'binom_one', kind: 'lemma', at: '3.2', sig: 'Bool.toNat <$> coin p = binom p 1', en: 'Proved by you in world 3, level 2.', de: 'Von dir bewiesen in Welt 3, Level 2.' },
    { name: "binom_succ'", kind: 'lemma', at: '3.3', sig: "(do let X ← binom p n; let Y ← coin p; pure (X + Y.toNat)) = binom p (n + 1)", en: 'Proved by you in world 3, level 3.', de: 'Von dir bewiesen in Welt 3, Level 3.' },
    { name: 'binom_add', kind: 'lemma', at: '3.5', sig: '(do let X ← binom p n; let Y ← binom p m; pure (X + Y)) = binom p (n + m)', en: 'Proved by you: the boss of world 3.', de: 'Von dir bewiesen: der Endgegner von Welt 3.' },
  ]
  Object.assign(DE, {
    Proof: 'Beweis', 'Run': 'Ausführen', 'Inventory': 'Inventar', Tactics: 'Taktiken', Theorems: 'Sätze',
    'Proved!': 'Bewiesen!', 'Goal': 'Ziel', 'goal {i} of {n}': 'Ziel {i} von {n}', 'Lean is thinking …': 'Lean denkt …',
    'Your lemma {x} is now in your inventory.': 'Dein Lemma {x} ist jetzt in deinem Inventar.',
    'To the proof ↓': 'Zum Beweis ↓', 'Insert': 'Einsetzen', 'Remove the last line': 'Letzte Zeile entfernen',
    'The proof needs Lean: open the game with ?backend=… (the address of a bridge).': 'Der Beweis braucht Lean: Öffne das Spiel mit ?backend=… (der Adresse einer Bridge).',
    'Lean cannot be reached: {e}': 'Lean ist nicht erreichbar: {e}',
    '{x} is not unlocked yet.': '{x} ist noch nicht freigeschaltet.',
    '{x} is not in your inventory.': '{x} ist nicht in deinem Inventar.',
    'This tactic is not in your inventory: {x}': 'Diese Taktik ist nicht in deinem Inventar: {x}',
    'Statement': 'Aussage', 'a tactic, e.g. rw [coin_not]': 'eine Taktik, z. B. rw [coin_not]',
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
  const atLeast = (a, b) => { const [x, y] = a.split('.').map(Number), [u, v] = b.split('.').map(Number); return x > u || (x === u && y >= v) }

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
    // the inventory at this level: what was introduced up to here; the lemma of this level is not yet
    available(item) { return atLeast(this.no, item.at) && !(item.kind === 'lemma' && item.at === this.no) }

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
        const tac = /^(rw|simp only|rfl|congr|funext|cases|induction')(?=\s|\[|$)/.exec(t)?.[1]
        const item = INVENTORY.find(i => i.name === tac)
        if (!item || !this.available(item)) return tr('This tactic is not in your inventory: {x}', { x: t.split(/\s/)[0] || t })
        const inside = /\[(.*)\]/.exec(t)?.[1]
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
    // a tapped item goes into the input: a rule into the brackets of rw/simp only, or as rw [rule]
    insert(item) {
      let v = this.input.value
      if (item.kind === 'tactic') v = item.name === '<;>' ? v + item.insert : (v.trim() ? v : item.insert)
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
      const parts = [head, ...this.texts, stmt]
      if (!BACKEND) { parts.push(el('div', 'pg-info pg-warn', tr('The proof needs Lean: open the game with ?backend=… (the address of a bridge).'))); this.box.replaceChildren(...parts); return }

      // the lines so far, and the goals now
      const hist = el('ol', 'pg-proof-lines')
      this.lines.forEach(l => hist.append(el('li', '', l)))
      const goals = el('div', 'pg-goals')
      if (this.done) goals.append(el('div', 'pg-proof-done', '✓ ' + tr('Proved!') + (this.lemma ? ' ' + tr('Your lemma {x} is now in your inventory.', { x: this.lemma }) : '')))
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
      this.input.placeholder = tr('a tactic, e.g. rw [coin_not]')
      this.input.value = this.typed ?? ''
      this.input.addEventListener('input', () => { this.typed = this.input.value })
      this.input.addEventListener('keydown', e => { if (e.key === 'Enter') { e.preventDefault(); this.run() } })
      const run = el('button', 'pg-check', tr('Run')); run.type = 'button'; run.disabled = this.busy || this.done
      run.addEventListener('click', () => this.run())
      row.append(this.input, run)
      const tools = el('div', 'pg-tools')
      const back = el('button', 'pg-tool', '↶ ' + tr('Remove the last line')); back.type = 'button'; back.disabled = this.busy || !this.lines.length
      back.addEventListener('click', () => this.back())
      tools.append(back)

      // the inventory
      const inv = el('div', 'pg-inventory')
      inv.append(el('div', 'pg-moves-head', tr('Inventory')))
      for (const [kind, title] of [['tactic', tr('Tactics')], ['rule', tr('Theorems')]]) {
        const group = el('div', 'pg-inv-group')
        group.append(el('span', 'pg-inv-title', title + ':'))
        for (const item of INVENTORY.filter(i => (kind === 'tactic' ? i.kind === 'tactic' : i.kind !== 'tactic') && this.available(i))) {
          const b = el('button', 'pg-chip' + (item.kind === 'lemma' ? ' pg-chip-lemma' : '') + (this.picked === item.name ? ' pg-chip-on' : '') + (item.at === this.no ? ' pg-chip-new' : ''), item.name)
          b.type = 'button'
          b.addEventListener('click', () => { this.picked = this.picked === item.name ? null : item.name; this.render() })
          group.append(b)
        }
        inv.append(group)
      }
      const it = INVENTORY.find(i => i.name === this.picked)
      if (it) {
        const doc = el('div', 'pg-inv-doc')
        doc.append(el('code', 'pg-inv-sig', it.sig), el('div', '', LANG === 'de' ? it.de : it.en))
        const ins = el('button', 'pg-tool', tr('Insert')); ins.type = 'button'
        ins.addEventListener('click', () => this.insert(it))
        doc.append(ins)
        inv.append(doc)
      }

      parts.push(hist, goals, err)
      if (!this.done) parts.push(row, tools)
      parts.push(inv)
      if (this.done) {
        const next = el('button', 'pg-next', tr('Next level ›')); next.type = 'button'
        next.addEventListener('click', () => this.level.onNextLevel?.())
        parts.push(next)
      }
      this.box.replaceChildren(...parts)
    }
  }

  // ---------------------------------------------------------------- the stage

  function stage() {
    const roots = [...document.querySelectorAll('.pg-level')]
    if (!roots.length) return
    const top = el('div', 'pg-top'), dots = el('div', 'pg-dots'), langs = el('div', 'pg-langs')
    for (const l of ['en', 'de']) {
      const b = el('button', 'pg-langbtn' + (LANG === l ? ' pg-current' : ''), l.toUpperCase())
      b.type = 'button'
      b.addEventListener('click', () => { LANG = l; try { localStorage.setItem('pg:lang', l) } catch {}; applyLang(); levels.forEach(x => { x.render(); x.proof?.render() }); refresh(); langs.querySelectorAll('button').forEach(x => x.classList.toggle('pg-current', x === b)) })
      langs.append(b)
    }
    top.append(langs, dots)
    roots[0].before(top)
    let current = 0
    const levels = roots.map((r, i) => new (r.classList.contains('pg-build') ? Builder : Level)(r, i, () => refresh()))
    // the proofs, below the boards
    levels.forEach(l => { if (l.root.dataset.proof) l.proof = new Proof(l, () => refresh()) })
    // a level is done when its board is solved and its statement proved
    const done = l => l.solved && (!l.proof || l.proof.proved)
    const refresh = () => {
      dots.replaceChildren()
      levels.forEach((l, k) => {
        l.proof?.update()
        const d = el('button', 'pg-dot' + (done(l) ? ' pg-dot-done' : l.solved ? ' pg-dot-half' : '') + (k === current ? ' pg-dot-current' : ''))
        d.type = 'button'
        d.title = tr('Level {i} of {n}', { i: k + 1, n: levels.length })
        d.addEventListener('click', () => show(k))
        dots.append(d)
      })
    }
    const show = k => {
      current = Math.max(0, Math.min(levels.length - 1, k))
      roots.forEach((r, i) => { r.hidden = i !== current })
      history.replaceState(null, '', `${location.pathname}${location.search}#level-${current + 1}`)
      refresh()
    }
    levels.forEach((l, k) => { l.onNextLevel = () => { show(k + 1); scrollTo({ top: roots[current].getBoundingClientRect().top + scrollY - 80, behavior: 'smooth' }) }; l.onNext = () => (l.proof ? l.proof.focus() : l.onNextLevel()) })
    const fromHash = Number(/^#level-(\d+)$/.exec(location.hash)?.[1] ?? 0) - 1
    show(fromHash >= 0 ? fromHash : Math.max(0, levels.findIndex(l => !done(l))))
  }

  function init() {
    applyLang()
    stage()
  }
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init)
  else init()
})()
