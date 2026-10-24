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

  // A backend with Lean (repl/bridge.py of nng-verso, with the journal's DiscreteMeasure as base):
  // `?backend=http://127.0.0.1:8091` in the address (kept; `?backend=` switches it off). After each
  // move it normalises the state with the rules of the world; a level is solved when the state and
  // the target have the same normal form, for every p.
  const BACKEND = (() => {
    try {
      const q = new URLSearchParams(location.search).get('backend')
      if (q !== null) { if (q) localStorage.setItem('pg:backend', q); else localStorage.removeItem('pg:backend') }
      return localStorage.getItem('pg:backend')
    } catch { return null }
  })()
  const RULES = "coin_not', unitInterval.symm_symm, ProbGame.coin_map_const, ProbGame.map_fun_id, map_pure, Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false"
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
      const w = 200, h = 150, base = 120, bh = 95, gap = Math.min(70, (w - 30) / Math.max(1, ks.length)), x0 = w / 2 - (gap * (ks.length - 1)) / 2, bw = Math.min(40, gap - 10)
      const g = svg('svg', { viewBox: `0 0 ${w} ${h}`, class: 'pg-target-svg' })
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

      const lean = el('pre', 'pg-lean', this.leanState())
      // what Lean makes of the state: its normal form
      const ln = el('div', 'pg-lean-state')
      if (!BACKEND) ln.textContent = tr('Lean is not connected: the board checks for every p by itself, without Lean.')
      else if (!this.leanNow) ln.textContent = tr('Lean is normalising …')
      else if (this.leanNow.error) ln.textContent = `Lean: ${this.leanNow.error.message}`
      else {
        ln.append(el('span', 'pg-lean-label', tr('Lean:') + ' '), el('code', '', this.leanNow.result))
        if (sameDist(d, this.target) && this.leanAgrees() === false) ln.append(el('div', 'pg-warn', `${tr('Lean disagrees: the target is')} ${this.leanGoal.result}`))
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
        const statement = this.leanAgrees() ? `${this.leanState()} = ${this.leanGoal.result}` : this.leanStatement
        if (statement) {
          box.append(el('div', 'pg-solved-lean-head', tr('In Lean, for every p:')))
          box.append(el('pre', 'pg-lean', statement))
        }
        const next = el('button', 'pg-next', tr('Next level ›'))
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
    not: { arity: 1, from: 'bool', to: 'bool', f: ([a]) => !a, show: ([a]) => `¬${a}`, lean: ([a]) => `!${a}`, label: 'not (¬)' },
    and: { arity: 2, more: true, from: 'bool', to: 'bool', f: xs => xs.every(x => x), show: xs => xs.join(' ∧ '), lean: xs => xs.join(' && '), label: 'and (∧)' },
    or: { arity: 2, more: true, from: 'bool', to: 'bool', f: xs => xs.some(x => x), show: xs => xs.join(' ∨ '), lean: xs => xs.join(' || '), label: 'or (∨)' },
    xor: { arity: 2, more: true, from: 'bool', to: 'bool', f: xs => xs.filter(x => x).length % 2 === 1, show: xs => xs.join(' ⊕ '),
      lean: xs => xs.slice(1).reduce((e, x) => `xor (${e}) ${x}`, xs[0]), label: 'xor (⊕)' },
    toNat: { arity: 1, from: 'bool', to: 'nat', f: ([a]) => (a ? 1 : 0), show: ([a]) => `𝟙(${a})`, lean: ([a]) => `${a}.toNat`, label: 'toNat: false = 0, true = 1' },
    count: { arity: 1, more: true, from: 'bool', to: 'nat', f: xs => xs.filter(x => x).length, show: xs => `#(${xs.join(', ')})`,
      lean: xs => `[${xs.join(', ')}].count true`, label: 'number of true' },
    add: { arity: 2, more: true, from: 'nat', to: 'nat', f: xs => xs.reduce((a, b) => a + b, 0), show: xs => xs.join(' + '), lean: xs => xs.join(' + '), label: 'add (+)' },
    max: { arity: 2, more: true, from: 'nat', to: 'nat', f: xs => Math.max(...xs), show: xs => `max(${xs.join(', ')})`,
      lean: xs => xs.slice(1).reduce((e, x) => `max (${e}) ${x}`, xs[0]), label: 'maximum' },
  }
  Object.assign(DE, {
    'not (¬)': 'nicht (¬)', 'and (∧)': 'und (∧)', 'or (∨)': 'oder (∨)', 'xor (⊕)': 'genau eins (⊕)', 'add (+)': 'addieren (+)',
    'number of true': 'Anzahl true', maximum: 'Maximum', 'new p-coin': 'neue p-Münze', Check: 'Prüfen', 'Remove the last': 'Letztes entfernen',
    '{n} left': 'noch {n}', 'Building blocks': 'Bausteine',
    'Lay down a coin with “new p-coin”. Tap cards to choose them (in this order), then a function.': 'Leg mit „neue p-Münze“ eine Münze hin. Tippe Karten an, um sie auszuwählen (in dieser Reihenfolge), dann eine Funktion.',
    'Choose {n} cards first (tap them).': 'Wähle erst {n} Karten aus (antippen).', 'Choose at least {n} cards first (tap them).': 'Wähle erst mindestens {n} Karten aus (antippen).',
    'This function needs coins (true/false).': 'Diese Funktion braucht Münzen (true/false).', 'This function needs numbers.': 'Diese Funktion braucht Zahlen.',
    'No more coins in this level.': 'In diesem Level gibt es keine weiteren Münzen.', 'There is nothing to check yet.': 'Es gibt noch nichts zu prüfen.',
    'Checked: {x}. It lives on {a}, the target on {b}.': 'Geprüft: {x}. Es lebt auf {a}, das Ziel auf {b}.',
    'Checked: {x}. At {k} it has P = {m}, the target {t}.': 'Geprüft: {x}. Bei {k} hat es P = {m}, das Ziel {t}.',
    'Checked: {x}, the selected card (or else the newest).': 'Geprüft wird {x}: die ausgewählte Karte (sonst die neueste).',
    'As a do block in Lean:': 'Als do-Block in Lean:',
    'Task: build the target from coins:': 'Aufgabe: Bau das Ziel aus Münzen:',
  })
  const funLabel = f => tr(FUNS[f].label)

  class Builder {
    constructor(root, index, onSolved) {
      this.root = root; this.index = index; this.onSolved = onSolved
      this.target = parseDist(root.dataset.target)
      this.funs = root.dataset.moves.split(',').map(x => x.trim()).filter(x => FUNS[x])
      this.maxCoins = Number(root.dataset.coins || 0) || Infinity
      this.board = root.querySelector('.pg-board')
      this.key = `pg:${location.pathname}:${index}`
      this.nodes = []      // { coin: true } or { fun, inputs: [indices] }
      try { this.nodes = JSON.parse(localStorage.getItem(this.key + ':tree') ?? '[]') } catch {}
      this.selected = []   // indices, in the order chosen
      this.checked = null  // { node, ok }
      this.message = ''
      addEventListener('resize', () => this.wires())
      this.render()
    }

    get solved() { try { return localStorage.getItem(this.key) === '1' } catch { return false } }
    save() { try { localStorage.setItem(this.key + ':tree', JSON.stringify(this.nodes)) } catch {} }

    // names: coins M1, M2, …; results Z1, Z2, …
    name(i) {
      const n = this.nodes[i], k = this.nodes.slice(0, i + 1).filter(x => !!x.coin === !!n.coin).length
      return (n.coin ? 'M' : 'Z') + k
    }
    space(i) { const n = this.nodes[i]; return n.coin ? 'bool' : FUNS[n.fun].to }
    depth(i) { const n = this.nodes[i]; return n.coin ? 0 : 1 + Math.max(...n.inputs.map(j => this.depth(j))) }
    // the nodes below i (with i), in their order
    below(i) {
      const seen = new Set(), go = j => { if (seen.has(j)) return; seen.add(j); (this.nodes[j].inputs ?? []).forEach(go) }
      go(i)
      return [...seen].sort((a, b) => a - b)
    }
    // the distribution of node i: all outcomes of the coins below it, each with its mass
    dist(i) {
      const coins = this.below(i).filter(j => this.nodes[j].coin), mass = new Map()
      for (let mask = 0; mask < 2 ** coins.length; mask++) {
        const val = new Map(), out = new Map(coins.map((c, b) => [c, !!(mask >> b & 1)]))
        let w = ONE
        for (const c of coins) w = w.mul(out.get(c) ? PP : complement(PP))
        const v = j => {
          if (out.has(j)) return out.get(j)
          if (!val.has(j)) { const n = this.nodes[j]; val.set(j, FUNS[n.fun].f(n.inputs.map(v))) }
          return val.get(j)
        }
        const k = String(v(i))
        mass.set(k, (mass.get(k) ?? ZERO).add(w))
      }
      for (const [k, m] of mass) if (m.zero) mass.delete(k)
      return { space: this.space(i), mass }
    }
    // the formula of a result, in the names of its inputs
    formula(i) { const n = this.nodes[i]; return n.coin ? '' : FUNS[n.fun].show(n.inputs.map(j => this.name(j))) }
    // node i as a do block of DiscreteMeasure
    lean(i) {
      const lines = this.below(i).map(j => {
        const n = this.nodes[j], x = this.name(j).toLowerCase()
        return n.coin ? `  let ${x} ← coin p` : `  let ${x} := ${FUNS[n.fun].lean(n.inputs.map(k => this.name(k).toLowerCase()))}`
      })
      return ['do', ...lines, `  return ${this.name(i).toLowerCase()}`].join('\n')
    }

    changed() { this.checked = null; this.message = ''; this.save(); this.render() }
    addCoin() {
      if (this.nodes.filter(n => n.coin).length >= this.maxCoins) { this.message = tr('No more coins in this level.'); this.render(); return }
      this.nodes.push({ coin: true }); this.selected = [this.nodes.length - 1]; this.changed()
    }
    apply(f) {
      const F = FUNS[f], sel = this.selected
      const bad = sel.length < F.arity || (!F.more && sel.length > F.arity) ? tr(F.more ? 'Choose at least {n} cards first (tap them).' : 'Choose {n} cards first (tap them).', { n: F.arity })
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

    // a small picture of a distribution
    chart(d, cls) {
      const ks = axis(d.space, [...d.mass.keys()]), gap = Math.max(50, ...ks.map(k => String(d.mass.get(k) ?? ZERO).length * 6.2 + 8)), w = Math.max(104, gap * ks.length + 6), h = 84, base = 66, bh = 44
      const g = svg('svg', { viewBox: `0 0 ${w} ${h}`, class: 'pg-mini ' + cls, width: w, height: h })
      g.append(svg('line', { x1: 4, x2: w - 4, y1: base, y2: base, class: 'pg-axis' }))
      const x0 = w / 2 - (gap * (ks.length - 1)) / 2, bw = Math.min(30, gap - 14)
      ks.forEach((k, j) => {
        const m = d.mass.get(k) ?? ZERO, x = x0 + j * gap, hh = m.value(P) * bh
        if (hh > 0) g.append(svg('rect', { class: 'pg-mini-sand', x: x - bw / 2, y: base - hh, width: bw, height: hh, rx: 2 }))
        g.append(svg('text', { x, y: base - hh - 4, 'text-anchor': 'middle', class: 'pg-mini-mass' }, m.toString()))
        g.append(svg('text', { x, y: base + 14, 'text-anchor': 'middle', class: 'pg-mini-point' }, pointName(d.space, k)))
      })
      return g
    }

    // the wires: from each input to its result, and from the checked node to the target
    wires() {
      const area = this.area, layer = this.layer
      if (!area || !area.isConnected || this.root.hidden) return
      const r0 = area.getBoundingClientRect()
      layer.setAttribute('viewBox', `0 0 ${r0.width} ${r0.height}`)
      layer.replaceChildren()
      const ok = this.checked?.ok ? new Set(this.below(this.checked.node)) : new Set()
      // the wires between cards stay inside the site (which may scroll)
      const rs = this.site.getBoundingClientRect(), clip = svg('clipPath', { id: `pg-clip-${this.index}` })
      clip.append(svg('rect', { x: rs.left - r0.left, y: rs.top - r0.top, width: rs.width, height: rs.height }))
      layer.append(clip)
      const line = (a, b, cls, inside = true) => {
        const x1 = a.right - r0.left, y1 = a.top + a.height / 2 - r0.top, x2 = b.left - r0.left, y2 = b.top + b.height / 2 - r0.top
        const mx = (x1 + x2) / 2
        const path = svg('path', { d: `M${x1},${y1} C${mx},${y1} ${mx},${y2} ${x2},${y2}`, class: 'pg-wire ' + cls })
        if (inside) path.setAttribute('clip-path', `url(#pg-clip-${this.index})`)
        layer.append(path)
      }
      this.nodes.forEach((n, i) => (n.inputs ?? []).forEach(j => {
        const a = this.cards[j]?.getBoundingClientRect(), b = this.cards[i]?.getBoundingClientRect()
        if (a && b) line(a, b, ok.has(i) ? 'pg-wire-ok' : '')
      }))
      if (this.checked) {
        const a = this.cards[this.checked.node]?.getBoundingClientRect(), b = this.targetBox.getBoundingClientRect()
        if (a && b.left > a.right && a.right <= this.site.getBoundingClientRect().right + 1) line(a, b, this.checked.ok ? 'pg-wire-ok' : 'pg-wire-bad', false)
      }
    }

    render() {
      const done = this.checked?.ok
      // the task
      const task = el('div', 'pg-task'), t = this.target
      const tk = axis(t.space, [...t.mass.keys()]).filter(k => !(t.mass.get(k) ?? ZERO).zero)
      task.append(el('b', '', tr('Task: build the target from coins:') + ' '),
        tk.length === 1 && (t.mass.get(tk[0]) ?? ZERO).eq(ONE) ? tr('surely {b}', { b: pointName(t.space, tk[0]) })
          : tk.map(k => `P(${pointName(t.space, k)}) = ${t.mass.get(k)}`).join(', '))

      // the building blocks
      const blocks = el('div', 'pg-blocks')
      blocks.append(el('div', 'pg-moves-head', tr('Building blocks')))
      const used = this.nodes.filter(n => n.coin).length
      const coin = el('button', 'pg-move pg-coin-btn', '+ ' + tr('new p-coin') + (this.maxCoins < Infinity ? ` (${tr('{n} left', { n: this.maxCoins - used })})` : ''))
      coin.type = 'button'; coin.disabled = used >= this.maxCoins
      coin.addEventListener('click', () => this.addCoin())
      blocks.append(coin)
      for (const f of this.funs) {
        const F = FUNS[f], fits = this.selected.length >= F.arity && (F.more || this.selected.length === F.arity) && this.selected.every(j => this.space(j) === F.from)
        const b = el('button', 'pg-move' + (fits ? '' : ' pg-move-off'), funLabel(f))
        b.type = 'button'
        b.addEventListener('click', () => this.apply(f))
        blocks.append(b)
      }

      // the site: a column per depth, a card per node
      const site = el('div', 'pg-site'), cols = []
      this.site = site
      this.cards = []
      this.nodes.forEach((n, i) => {
        const dp = this.depth(i)
        while (cols.length <= dp) { const c = el('div', 'pg-col'); cols.push(c); site.append(c) }
        const k = this.selected.indexOf(i), ok = done && this.below(this.checked.node).includes(i)
        const card = el('button', 'pg-card' + (k >= 0 ? ' pg-card-sel' : '') + (ok ? ' pg-card-ok' : '') + (this.checked?.node === i && !this.checked.ok ? ' pg-card-bad' : ''))
        card.type = 'button'
        const head = el('div', 'pg-card-head')
        head.append(el('b', '', this.name(i)), n.coin ? '' : ` = ${this.formula(i)}`)
        if (k >= 0) head.append(el('span', 'pg-card-badge', String(k + 1)))
        card.append(head, this.chart(this.dist(i), ''))
        card.dataset.node = String(i)
        card.addEventListener('click', () => this.pick(i))
        cols[dp].append(card)
        this.cards[i] = card
      })
      if (!this.nodes.length) site.append(el('div', 'pg-site-empty', tr('Lay down a coin with “new p-coin”. Tap cards to choose them (in this order), then a function.')))
      site.addEventListener('scroll', () => this.wires())

      // the target
      this.targetBox = el('div', 'pg-target-box' + (done ? ' pg-card-ok' : ''))
      this.targetBox.append(this.targetPicture())

      this.area = el('div', 'pg-build-area')
      this.layer = svg('svg', { class: 'pg-wires' })
      this.area.append(this.layer, site, this.targetBox)

      const tools = el('div', 'pg-tools')
      const check = el('button', 'pg-check', tr('Check')), undo = el('button', 'pg-tool', '↶ ' + tr('Remove the last')), reset = el('button', 'pg-tool', '⟲ ' + tr('Start over'))
      check.type = undo.type = reset.type = 'button'
      undo.disabled = reset.disabled = !this.nodes.length
      check.addEventListener('click', () => this.check())
      undo.addEventListener('click', () => this.removeLast()); reset.addEventListener('click', () => this.reset())
      tools.append(check, undo, reset)

      const info = el('div', 'pg-info' + (this.message ? ' pg-warn' : ''),
        this.message || (this.nodes.length ? tr('Checked: {x}, the selected card (or else the newest).', { x: this.name(this.selected.length === 1 ? this.selected[0] : this.nodes.length - 1) }) : ''))

      const slider = el('label', 'pg-slider')
      const input = el('input'); input.type = 'range'; input.min = '0.05'; input.max = '0.95'; input.step = '0.05'; input.value = String(P)
      input.addEventListener('input', () => { P = Number(input.value); try { localStorage.setItem('pg:p', input.value) } catch {}; this.render() })
      slider.append(`${tr('the picture for p =')} ${P.toFixed(2)} `, input, el('span', 'pg-slider-note', ' ' + tr('(only an example; the masses hold for every p)')))

      const parts = [task, blocks, this.area, tools, info, slider]
      if (done) {
        const box = el('div', 'pg-solved')
        box.append(el('div', 'pg-solved-head', '✓ ' + tr('Solved!')))
        box.append(el('div', 'pg-solved-lean-head', tr('As a do block in Lean:')))
        box.append(el('pre', 'pg-lean', this.lean(this.checked.node)))
        const next = el('button', 'pg-next', tr('Next level ›'))
        next.type = 'button'
        next.addEventListener('click', () => this.onNext?.())
        box.append(next)
        parts.push(box)
      }
      this.board.replaceChildren(...parts)
      requestAnimationFrame(() => this.wires())
    }
  }
  Builder.prototype.targetPicture = Level.prototype.targetPicture

  // ---------------------------------------------------------------- the stage

  function stage() {
    const roots = [...document.querySelectorAll('.pg-level')]
    if (!roots.length) return
    const top = el('div', 'pg-top'), dots = el('div', 'pg-dots'), langs = el('div', 'pg-langs')
    for (const l of ['en', 'de']) {
      const b = el('button', 'pg-langbtn' + (LANG === l ? ' pg-current' : ''), l.toUpperCase())
      b.type = 'button'
      b.addEventListener('click', () => { LANG = l; try { localStorage.setItem('pg:lang', l) } catch {}; applyLang(); levels.forEach(x => x.render()); refresh(); langs.querySelectorAll('button').forEach(x => x.classList.toggle('pg-current', x === b)) })
      langs.append(b)
    }
    top.append(langs, dots)
    roots[0].before(top)
    let current = 0
    const levels = roots.map((r, i) => new (r.classList.contains('pg-build') ? Builder : Level)(r, i, () => refresh()))
    const refresh = () => {
      dots.replaceChildren()
      levels.forEach((l, k) => {
        const d = el('button', 'pg-dot' + (l.solved ? ' pg-dot-done' : '') + (k === current ? ' pg-dot-current' : ''))
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
      levels[current].wires?.()
    }
    levels.forEach((l, k) => { l.onNext = () => show(k + 1) })
    const fromHash = Number(/^#level-(\d+)$/.exec(location.hash)?.[1] ?? 0) - 1
    show(fromHash >= 0 ? fromHash : Math.max(0, levels.findIndex(l => !l.solved)))
  }

  function init() {
    applyLang()
    stage()
  }
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init)
  else init()
})()
