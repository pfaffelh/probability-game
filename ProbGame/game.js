// The probability game: distributions as sand, moves as maps, the result as the image measure.
//
// Each `.pg-level` (from `::::level` in ProbGame/Level.lean) has a start distribution, a target and
// the moves offered. A distribution is a space ('bool', 'nat', 'int') with masses a + b·p (exact
// fractions a, b: the same for every p) on its points; the picture draws them for an example p,
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
    heads: 'Kopf', tails: 'Zahl', Moves: 'Züge', Undo: 'Zurück', 'Start over': 'Neu anfangen', 'Next level ›': 'Nächstes Level ›',
    'Solved!': 'Geschafft!', Target: 'Ziel', 'In Lean, for every p:': 'In Lean, für jedes p:', 'proved': 'bewiesen',
    'Tap a column to see where its sand came from.': 'Tippe eine Säule an, um zu sehen, woher ihr Sand kommt.',
    'This move needs a coin, not a number.': 'Dieser Zug braucht eine Münze, keine Zahl.',
    'Level {i} of {n}': 'Level {i} von {n}', 'nothing flows here': 'hierher fließt nichts',
    '{b}: the sand comes from {from}, P = {sum}{m}': '{b}: Der Sand kommt aus {from}, P = {sum}{m}',
    'flip': 'umdrehen', 'always heads': 'immer Kopf', 'always tails': 'immer Zahl', 'do nothing': 'nichts tun',
    'heads = 1, tails = 0': 'Kopf = 1, Zahl = 0', 'heads: win {a}, tails: {b}': 'Kopf: {a} gewinnen, Zahl: {b}',
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

  // A mass a + b·p, with exact fractions a and b: the same for every p.
  class Lin {
    constructor(a, b = new Q(0)) { this.a = a; this.b = b }
    add(o) { return new Lin(this.a.add(o.a), this.b.add(o.b)) }
    eq(o) { return this.a.eq(o.a) && this.b.eq(o.b) }
    get zero() { return this.a.zero && this.b.zero }
    value(p) { return this.a.value + this.b.value * p }
    toString() {
      const coef = q => (q.n === q.d ? '' : q.n === -q.d ? '−' : String(q).replace('-', '−'))
      if (this.b.zero) return String(this.a).replace('-', '−')
      const pt = `${coef(this.b)}p`
      if (this.a.zero) return pt
      return this.b.n < 0 ? `${this.a} − ${coef(neg(this.b))}p` : `${this.a} + ${pt}`
    }
  }
  // `p`, `1-p`, `1`, `0`, `1/2`, `2p`, `1-2p`
  const parseLin = str => {
    const t = str.replace(/\s/g, ''), i = t.indexOf('p')
    if (i < 0) return new Lin(parseQ(t))
    const cut = Math.max(t.lastIndexOf('+', i), t.lastIndexOf('-', i))
    const a = cut > 0 ? t.slice(0, cut) : '0', c = cut > 0 ? t.slice(cut, i) : t.slice(0, i)
    return new Lin(parseQ(a), c === '' || c === '+' ? new Q(1) : c === '-' ? new Q(-1) : parseQ(c))
  }
  const ONE = new Lin(new Q(1)), ZERO = new Lin(new Q(0))
  const complement = m => new Lin(new Q(1).add(neg(m.a)), neg(m.b))
  // the example p of the picture
  let P = 0.3
  try { P = Number(localStorage.getItem('pg:p') ?? 0.3) || 0.3 } catch {}

  // ---------------------------------------------------------------- distributions

  // A distribution: a space and the masses of its points (keys: 'true'/'false', or numbers as text).
  function parseDist(spec) {
    const w = spec.trim().split(/\s+/)
    if (w[0] === 'bernoulli') { const m = parseLin(w[1]); return { space: 'bool', mass: new Map([['true', m], ['false', complement(m)]]) } }
    if (w[0] === 'pure') return { space: /^-?\d+$/.test(w[1]) ? 'nat' : 'bool', mass: new Map([[w[1], ONE]]) }
    return { space: w[0], mass: new Map(w.slice(1).map(x => { const [k, q] = x.split(':'); return [k, parseLin(q)] })) }
  }
  const sameDist = (a, b) => {
    if (a.space !== b.space) return false
    const keys = new Set([...a.mass.keys(), ...b.mass.keys()])
    return [...keys].every(k => (a.mass.get(k) ?? ZERO).eq(b.mass.get(k) ?? ZERO))
  }
  // the points shown on the axis: a coin always shows both sides, tails left and heads right (as 0
  // and 1 on the numbers, so that renaming moves nothing sideways); numbers in their order
  const axis = (space, keys) => space === 'bool' ? ['false', 'true']
    : [...new Set(keys)].sort((x, y) => Number(x) - Number(y))
  const pointName = (space, k) => space === 'bool' ? tr(k === 'true' ? 'heads' : 'tails') : k
  const spaceName = s => ({ bool: 'Bool', nat: 'ℕ', int: 'ℤ' })[s]

  // ---------------------------------------------------------------- moves

  // A move: a map from one space to another, with its name and its Lean form.
  function parseMove(spec) {
    const w = spec.trim().split(/\s+/)
    switch (w[0]) {
      case 'id': return { from: 'bool', to: 'bool', f: k => k, lean: 'id', label: () => tr('do nothing') }
      case 'not': return { from: 'bool', to: 'bool', f: k => (k === 'true' ? 'false' : 'true'), lean: 'not', label: () => tr('flip') }
      case 'heads': return { from: 'bool', to: 'bool', f: () => 'true', lean: '(fun _ => true)', label: () => tr('always heads') }
      case 'tails': return { from: 'bool', to: 'bool', f: () => 'false', lean: '(fun _ => false)', label: () => tr('always tails') }
      case 'toNat': return { from: 'bool', to: 'nat', f: k => (k === 'true' ? '1' : '0'), lean: 'Bool.toNat', label: () => tr('heads = 1, tails = 0') }
      case 'payoff': {
        const [a, b] = [w[1], w[2]]
        return { from: 'bool', to: 'int', f: k => (k === 'true' ? a : b), lean: `(fun b => if b then (${a} : ℤ) else ${b})`,
          label: () => tr('heads: win {a}, tails: {b}', { a, b }) }
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
          const sum = pre.length > 1 ? `${pre.map(k => { const q = last.before.mass.get(k); return q.a.zero || q.b.zero ? String(q) : `(${q})` }).join(' + ')} = ` : ''
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
    const levels = roots.map((r, i) => new Level(r, i, () => refresh()))
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
