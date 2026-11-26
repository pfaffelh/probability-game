import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Multi-Stage Experiments" =>

%%%
htmlSplit := .never
%%%

:::en
Your task is always the same: fill the fields of the `bind` gate. `x` decides which map is chosen,
`y` determines the result.

Then a second stage: *which* coin `y` is, depends on what the coin `x` showed, as in a tree
diagram. In Lean: `do let x ← coin p; let y ← (bif x then coin q else coin r); …`.

This world is one of two ways after *Laws of `do`*; the other is *Counting*. They do not need
each other.
:::

:::de
Deine Aufgabe ist immer dieselbe: Füll die Felder des Bausteins `bind`. `x` entscheidet, welche
Abbildung gewählt wird, `y` bestimmt das Ergebnis.

Dann eine zweite Stufe: *Welche* Münze `y` ist, hängt davon ab, was die Münze `x` zeigte, wie
im Baumdiagramm. In Lean: `do let x ← coin p; let y ← (bif x then coin q else coin r); …`.

Diese Welt ist einer von zwei Wegen nach *Gesetze von `do`*; der andere ist *Zählen*. Sie brauchen
einander nicht.
:::

:::proofen
The statements are about the mass at `true`; your lemma `bind_true` from *Two Coins* goes both
ways: through `true` and through `false`.
:::

:::proofde
Die Aussagen handeln von der Masse bei `true`; dein Lemma `bind_true` aus *Zwei Münzen* geht beide
Wege: über `true` und über `false`.
:::

::::circuit (height := "540") (inputs := "x y") (gates := "") (table := "0001") (goal := "x && y") (proof := "(x y : Bool) : (bif x then y else false) = (x && y)") (start := "a=bind@240,250; x>a.0; y>a.1; a>out") (play := "a.T=id; a.F=false") (uses := "-")
:::en
*A gate of your own.* New gate: `bind`. `x` decides which map is chosen, `y` determines the result.
:::

:::de
*Ein eigener Baustein.* Neuer Baustein: `bind`. `x` entscheidet, welche Abbildung gewählt wird, `y`
bestimmt das Ergebnis.
:::

:::solution
```
revert x y
decide
```
:::
::::

::::circuit (height := "540") (inputs := "x y") (gates := "") (table := "0110") (goal := "x ^^ y") (proof := "(x y : Bool) : (bif x then !y else y) = (x ^^ y)") (start := "a=bind@240,250; x>a.0; y>a.1; a>out") (play := "a.T=not; a.F=id") (uses := "-")
:::hint (anchor := "none")
:::

:::en
*xor, chosen yourself.* `true` when exactly one input is. With `bind`: for `x = true` one map of `y`,
for `x = false` another. Four maps for each field: sixteen gates with two inputs, all of them.
:::

:::de
*xor, selbst gewählt.* `true`, wenn genau ein Eingang es ist. Mit `bind`: für `x = true` eine
Abbildung von `y`, für `x = false` eine andere. Vier Abbildungen für jedes Feld: sechzehn Bausteine mit
zwei Eingängen, alle.
:::
:::solution
```
revert x y
decide
```
:::
::::

::::circuit (height := "540") (inputs := "x y") (gates := "") (table := "1101") (goal := "!x || y") (proof := "(x y : Bool) : (bif x then y else true) = (!x || y)") (start := "a=bind@240,250; x>a.0; y>a.1; a>out") (play := "a.T=id; a.F=true") (uses := "-")
:::hint (anchor := "none")
:::

:::en
*If x, then y.* The implication: `false` only when `x` is `true` and `y` is `false`. In Lean
`!x || y`.
:::

:::de
*Wenn x, dann y.* Die Implikation: `false` nur, wenn `x` `true` ist und `y` `false`. In Lean
`!x || y`.
:::
:::solution
```
revert x y
decide
```
:::
::::

:::::circuit (height := "480") (inputs := "x y") (gates := "") (coins := "p ?|?") (target := "bool true:p^2 false:1-p^2") (start := "x>y.0; y>out") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← (bif x then coin p else pure false); pure y) true = (↑p * ↑p : ℝ≥0∞)") (play := "y.T=p; y.F=0") (uses := "bind_true, bind_false")
:::en
*Only after true.* `bind` for coins: the result of the coin `x` decides which coin is taken for the
next experiment.
:::

:::de
*Nur nach true.* `bind` für Münzen: Das Ergebnis der Münze `x` entscheidet, welche Münze für das
nächste Experiment genommen wird.
:::

:::proofen
`let y ← m; pure y` is just `m` (Lean drops it already when it reads the statement). The mass at
`true` comes two ways, `bind_true`; what is left is computing: which coin each way takes, its mass
at `true`, products and sums.
:::

:::proofde
`let y ← m; pure y` ist einfach `m` (Lean lässt es schon beim Lesen der Aussage weg). Die Masse bei
`true` kommt auf zwei Wegen, `bind_true`; was bleibt, ist Rechnen: welche Münze jeder Weg nimmt,
ihre Masse bei `true`, Produkte und Summen.
:::
:::solution
```
rw [bind_true]
simp
```
:::
:::::

:::::circuit (height := "480") (inputs := "x y") (gates := "") (coins := "p ?|?") (target := "bernoulli p") (start := "x>y.0; y>out") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← (bif x then pure true else pure false); pure y) true = (↑p : ℝ≥0∞)") (play := "y.T=1; y.F=0") (uses := "bind_true, bind_false")
:::en
*Copying.* `y` is surely `true` after `true`, and surely `false` after `false`: it copies `x`.
:::

:::de
*Abschreiben.* `y` ist sicher `true` nach `true` und sicher `false` nach `false`: Es schreibt `x` ab.
:::

:::proofen
As before; now both ways end in a point mass, `pure true` and `pure false`.
:::

:::proofde
Wie eben; jetzt enden beide Wege in einer Punktmasse, `pure true` und `pure false`.
:::
:::solution
```
rw [bind_true]
simp
```
:::
:::::

:::::circuit (height := "480") (inputs := "x y") (gates := "") (coins := "p ?|?") (target := "bool true:2p-p^2 false:(1-p)^2") (start := "x>y.0; y>out") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← (bif x then pure true else coin p); pure y) true = (↑p + ↑(σ p) * ↑p : ℝ≥0∞)") (play := "y.T=1; y.F=p") (uses := "bind_true, bind_false")
:::en
*One more try.* When `x` showed `true`, that is enough: `y` is surely `true`. When it showed `false`,
throw again. Compare with *At least one `true`* of *Laws of `do`*: the same as `x || y`, but the
second coin is only thrown when it is needed.
:::

:::de
*Noch ein Versuch.* Zeigte `x` `true`, reicht das: `y` ist sicher `true`. Zeigte es `false`, wirf noch
einmal. Vergleiche mit *Mindestens einmal `true`* aus *Gesetze von `do`*: dasselbe wie `x || y`, aber die
zweite Münze wird nur geworfen, wenn sie gebraucht wird.
:::

:::proofen
Two ways to `true` again, through `x = true` and through `x = false`: each has the mass of its first throw, times the mass of what follows at `true`.
:::

:::proofde
Wieder zwei Wege zu `true`, über `x = true` und über `x = false`: Jeder hat die Masse seines ersten Wurfs, mal die Masse dessen, was folgt, bei `true`.
:::
:::solution
```
rw [bind_true]
simp
```
:::
:::::

:::::circuit (height := "480") (inputs := "x y") (gates := "") (coins := "p ?|?") (target := "bool true:1-2p+2p^2 false:2p-2p^2") (start := "x>y.0; y>out") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← (bif x then coin p else coin (σ p)); pure y) true = (↑p * ↑p + ↑(σ p) * ↑(σ p) : ℝ≥0∞)") (play := "y.T=p; y.F=1-p") (uses := "bind_true, bind_false")
:::en
*A coin that remembers.* After `true` the coin `p` again, after `false` the flipped coin $`1 - p`:
the second throw tends to repeat the first.
:::

:::de
*Eine Münze, die sich erinnert.* Nach `true` wieder die Münze `p`, nach `false` die umgedrehte Münze
$`1 - p`: Der zweite Wurf wiederholt eher den ersten.
:::

:::proofen
Two different coins in the two ways now, `coin p` and `coin (σ p)`; `simp` knows the masses of
both.
:::

:::proofde
Jetzt zwei verschiedene Münzen in den zwei Wegen, `coin p` und `coin (σ p)`; `simp` kennt die
Massen beider.
:::
:::solution
```
rw [bind_true]
simp
```
:::
:::::

:::::circuit (inputs := "x y z") (gates := "") (coins := "p ?|? ?|?") (target := "bernoulli p") (start := "x>y.0; y>z.0; z>out") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← (bif x then pure false else pure true); let z ← (bif y then pure false else pure true); pure z) true = (↑p : ℝ≥0∞)") (play := "y.T=0; y.F=1; z.T=0; z.F=1") (uses := "bind_true, bind_false")
:::en
*A chain: flip, and flip back.* A *Markov chain* goes step by step, and each step depends only on
where the chain is now: `y` comes after `x`, `z` after `y`. Make each step flip: from `true` to
`false`, from `false` to `true`. Where is the chain after two steps?
:::

:::de
*Eine Kette: umdrehen, und zurück.* Eine *Markov-Kette* geht Schritt für Schritt, und jeder Schritt
hängt nur davon ab, wo die Kette gerade ist: `y` kommt nach `x`, `z` nach `y`. Lass jeden Schritt
umdrehen: von `true` nach `false`, von `false` nach `true`. Wo ist die Kette nach zwei
Schritten?
:::

:::proofen
What follows the first coin is a `do` block again, inside the computation, where `rw` would have to
pick the right place. A rule can be given to `simp` instead, `simp [h]`: it uses it wherever it
fits.
:::

:::proofde
Was auf die erste Münze folgt, ist wieder ein `do`-Block, mitten in der Rechnung, wo `rw` die
richtige Stelle treffen müsste. Eine Regel kann man stattdessen `simp` geben, `simp [h]`: Es benutzt
sie, wo sie passt.
:::
:::solution
```
rw [bind_true]
simp [bind_true]
```
:::
:::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) : (do let x ← μ; let y ← pure (!x); pure (!y)) = μ") (new := "pure_bind") (uses := "pure_bind, Bool.not_not, bind_pure")
:::en
*Flip back, from any start.* The chain of the last board, for every start: whatever the start `μ`, after two flips the distribution is `μ` again.
:::

:::de
*Zurückdrehen, von jedem Start.* Die Kette des letzten Spielfelds, für jeden Start: Was auch immer der Start `μ` ist, nach zweimal Umdrehen ist die Verteilung wieder `μ`.
:::

:::proofen
Each step is sure: `pure_bind : (do let x ← pure a; f x) = f a`. What is left you know from *Bool*
and *Two Coins*; all of it under the `do`.
:::

:::proofde
Jeder Schritt ist sicher: `pure_bind : (do let x ← pure a; f x) = f a`. Was bleibt, kennst du aus
*Bool* und *Zwei Münzen*; alles unter dem `do`.
:::
:::solution
```
simp only [pure_bind, Bool.not_not, bind_pure]
```
:::
::::

::::leanonly (proof := "(p q r : I) : (do let x ← coin p; bif x then coin q else coin r) true = (↑p * ↑q + ↑(σ p) * ↑r : ℝ≥0∞)") (uses := "bind_true, bind_false")
:::en
*One step forward.* A chain starts with `coin p`. From `true` the next step is `coin q`, from `false` it is `coin r`. The start distribution is carried one step forward: at `true` arrives $`p q + (1 - p) r`.
:::

:::de
*Ein Schritt nach vorn.* Eine Kette startet mit `coin p`. Von `true` aus ist der nächste Schritt `coin q`, von `false` aus `coin r`. Die Startverteilung wird einen Schritt nach vorn getragen: Bei `true` kommt $`p q + (1 - p) r` an.
:::

:::proofen
As on the boards before: split by the first coin, then compute.
:::

:::proofde
Wie auf den Spielfeldern davor: nach der ersten Münze teilen, dann rechnen.
:::
:::solution
```
rw [bind_true]
simp
```
:::
::::

::::leanonly (proof := "(p q r : I) : (do let x ← coin p; bif x then coin q else coin r) false = (↑p * ↑(σ q) + ↑(σ p) * ↑(σ r) : ℝ≥0∞)") (new := "bind_false") (uses := "bind_false, bind_true")
:::en
*...and at false.* The rest of the distribution after the step: at `false` arrives $`p (1 - q) + (1 - p)(1 - r)`. Now the whole distribution after one step is known.
:::

:::de
*...und bei false.* Der Rest der Verteilung nach dem Schritt: Bei `false` kommt $`p (1 - q) + (1 - p)(1 - r)` an. Jetzt ist die ganze Verteilung nach einem Schritt bekannt.
:::

:::proofen
`bind_false : (do let x ← μ; f x) false = μ true * f true false + μ false * f false false`.
:::

:::proofde
`bind_false : (do let x ← μ; f x) false = μ true * f true false + μ false * f false false`.
:::
:::solution
```
rw [bind_false]
simp
```
:::
::::

::::leanonly (proof := "(p q r : I) (h : ↑p * ↑q + ↑(σ p) * ↑r = (↑p : ℝ≥0∞)) : (do let x ← coin p; bif x then coin q else coin r) = coin p") (uses := "bool_ext, bind_true, bind_false")
:::en
*A distribution that stays.* When does the step carry `coin p` to itself? When the mass at `true` after the step is $`p` again: $`p = p q + (1 - p) r`. Then `coin p` is *stationary*: the chain started there stays there, step after step.
:::

:::de
*Eine Verteilung, die bleibt.* Wann trägt der Schritt `coin p` zu sich selbst? Wenn die Masse bei `true` nach dem Schritt wieder $`p` ist: $`p = p q + (1 - p) r`. Dann ist `coin p` *stationär*: Die dort gestartete Kette bleibt dort, Schritt für Schritt.
:::

:::proofen
Two distributions on `Bool` with the same mass at `true` are the same. Then the computation of *One
step forward*, and the hypothesis `h`.
:::

:::proofde
Zwei Verteilungen auf `Bool` mit derselben Masse bei `true` sind gleich. Dann die Rechnung aus *Ein
Schritt nach vorn*, und die Annahme `h`.
:::
:::solution
```
apply bool_ext
rw [bind_true]
simp
exact h
```
:::
::::

::::circuit (height := "480") (inputs := "x y") (gates := "") (coins := "p ?|?") (target := "bernoulli 1-p") (start := "x>y.0; y>out") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← (bif x then coin (σ p) else coin (σ p)); pure y) true = (↑(σ p) : ℝ≥0∞)") (new := "cond_same") (play := "y.T=1-p; y.F=1-p") (uses := "cond_same, coin_unused, coin_true, prob_unused, coin_false, coin_total")
:::en
*A chain that forgets.* The target is `coin (1 - p)`, whatever `x` shows. Fill both fields of `y`
with the same coin: then it does not matter where the chain was, and the start is forgotten after
one step.
:::

:::de
*Eine Kette, die vergisst.* Das Ziel ist `coin (1 - p)`, was auch immer `x` zeigt. Füll beide Felder
von `y` mit derselben Münze: Dann spielt es keine Rolle, wo die Kette war, und der Start ist nach einem
Schritt vergessen.
:::

:::proofen
Both branches are the same: `cond_same : (bif c then a else a) = a`, here under the `do`. Then the
coin `x` is not used.
:::

:::proofde
Beide Zweige sind gleich: `cond_same : (bif c then a else a) = a`, hier unter dem `do`. Dann wird
die Münze `x` nicht benutzt.
:::
:::solution
```
simp only [cond_same]
rw [coin_unused, coin_true]
```
:::
::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] (q : I) : (do let x ← μ; bif x then coin q else coin q) = coin q") (new := "prob_unused") (uses := "cond_same, prob_unused, coin_unused")
:::en
*Forgetting, from any start.* If the next step does not depend on where the chain is (`q = r`), one step is enough to forget the start: whatever `μ` was, after the step it is `coin q`.
:::

:::de
*Vergessen, von jedem Start.* Hängt der nächste Schritt nicht davon ab, wo die Kette ist (`q = r`), genügt ein Schritt, um den Start zu vergessen: Was auch immer `μ` war, nach dem Schritt ist es `coin q`.
:::

:::proofen
`cond_same` as on the last board, and `prob_unused : (do let _ ← μ; ν) = ν` for any distribution `μ` (`[Prob μ]`), not only a coin.
:::

:::proofde
`cond_same` wie auf dem letzten Spielfeld, und `prob_unused : (do let _ ← μ; ν) = ν` für jede Verteilung `μ` (`[Prob μ]`), nicht nur eine Münze.
:::
:::solution
```
simp only [cond_same]
rw [prob_unused]
```
:::
::::

::::circuit (inputs := "x y z") (gates := "") (coins := "p ?|? ?|?") (target := "bool true:3p-3p^2+p^3 false:(1-p)^3") (start := "x>y.0; y>z.0; z>out") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← (bif x then pure true else coin p); let z ← (bif y then pure true else coin p); pure z) true = (↑p + ↑(σ p) * (↑p + ↑(σ p) * ↑p) : ℝ≥0∞)") (play := "y.T=1; y.F=p; z.T=1; z.F=p") (uses := "bind_true, bind_false")
:::en
*Boss: three tries.* Throw until `true` comes, at most three times. `y` comes after `x`, and `z` after `y`. `false` only when all three tries fail: $`(1 - p)^3`.
:::

:::de
*Boss: drei Versuche.* Wirf, bis `true` kommt, höchstens dreimal. `y` kommt nach `x`, und `z` nach `y`. `false` nur, wenn alle drei Versuche scheitern: $`(1 - p)^3`.
:::
:::solution
```
rw [bind_true]
simp [bind_true]
```
:::
::::
