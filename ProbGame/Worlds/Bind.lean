import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Coins that Wait" =>

%%%
htmlSplit := .never
%%%

:::en
Until now all coins were thrown at once, independently. Now a coin waits: it is thrown *after* the
coin `x`, and **which** coin it is depends on a wire. The coin `y` on the left has an input of its
own: wire `x` into it, and `y` becomes `bif x then coin q else coin r`, the coin `q` when `x` showed
`true`, the coin `r` when it showed `false`. This is the `bind` gate of the world *Circuits*, now
with distributions in its two fields: first throw `x`, then, depending on what came, throw the one or
the other coin. In Lean: `do let x ← coin p; let y ← (bif x then coin q else coin r); …`, that is
`coin p >>= fun x => …`.

A row of the table has a mass only once `y` is wired; the mass of `y` in a row is that of the coin
the wire chose.
:::

:::de
Bisher wurden alle Münzen auf einmal geworfen, unabhängig. Jetzt wartet eine Münze: Sie wird *nach*
der Münze `x` geworfen, und **welche** Münze es ist, hängt an einem Draht. Die Münze `y` links hat einen
eigenen Eingang: Verdrahte `x` mit ihm, und `y` wird zu `bif x then coin q else coin r`, die Münze `q`,
wenn `x` `true` zeigte, die Münze `r`, wenn es `false` zeigte. Das ist der Baustein `bind` der Welt
*Schaltungen*, jetzt mit Verteilungen in seinen zwei Feldern: erst `x` werfen, dann, je nachdem was kam,
die eine oder die andere Münze. In Lean: `do let x ← coin p; let y ← (bif x then coin q else coin r); …`,
also `coin p >>= fun x => …`.

Eine Zeile der Tafel hat erst eine Masse, wenn `y` verdrahtet ist; die Masse von `y` in einer Zeile ist
die der Münze, die der Draht gewählt hat.
:::

:::proofen
The statements are about the mass at `true`: the board shows the whole distribution, and your lemma
`bool_ext` says that the mass at `true` decides it. The new rule
`bind_true : (μ >>= f) true = μ true * f true true + μ false * f false true` goes both ways: through
`true` (the mass `μ true`, then the mass of `f true` at `true`) and through `false`.
:::

:::proofde
Die Aussagen handeln von der Masse bei `true`: Das Spielfeld zeigt die ganze Verteilung, und dein Lemma
`bool_ext` sagt, dass die Masse bei `true` sie festlegt. Die neue Regel
`bind_true : (μ >>= f) true = μ true * f true true + μ false * f false true` geht beide Wege: über
`true` (die Masse `μ true`, dann die Masse von `f true` bei `true`) und über `false`.
:::

::::circuit (inputs := "x y") (gates := "and, or, not") (coins := "p p|0") (target := "bool true:p^2 false:1-p^2") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← (bif x then coin p else pure false); pure y) true = (↑p * ↑p : ENNReal)") (new := "bind_true, mul_zero") (play := "x>y.0; y>out")
:::en
*Only after true.* `y` is a coin when `x` showed `true`, and surely `false` otherwise. Wire `x` into
`y`, and `y` to the output. Compare with *Both `true`* of *Building with Coins*: the same distribution,
without an `and`.
:::

:::de
*Nur nach true.* `y` ist eine Münze, wenn `x` `true` zeigte, und sonst sicher `false`. Verdrahte `x` mit
`y` und `y` mit dem Ausgang. Vergleiche mit *Beide `true`* aus *Bauen mit Münzen*: dieselbe Verteilung,
ohne ein `and`.
:::

:::proofen
`let y ← m; pure y` is just `m` (Lean drops it already when it reads the statement). `rw [bind_true]`
splits the mass at `true` into the two ways, `Bool.cond_true` and `Bool.cond_false` choose the coin of
each way, and the rest is computing: `pure_true`, `Bool.cond_false`, and the new rule
`mul_zero : a * 0 = 0`, then `add_zero` and `coin_true`.

*Tip.* `rw [bind_true, Bool.cond_true, Bool.cond_false]`, then
`rw [pure_true, Bool.cond_false, mul_zero, add_zero, coin_true]`.
:::

:::proofde
`let y ← m; pure y` ist einfach `m` (Lean lässt es schon beim Lesen der Aussage weg). `rw [bind_true]`
teilt die Masse bei `true` in die zwei Wege, `Bool.cond_true` und `Bool.cond_false` wählen die Münze
jedes Wegs, und der Rest ist Rechnen: `pure_true`, `Bool.cond_false` und die neue Regel
`mul_zero : a * 0 = 0`, dann `add_zero` und `coin_true`.

*Tipp.* `rw [bind_true, Bool.cond_true, Bool.cond_false]`, dann
`rw [pure_true, Bool.cond_false, mul_zero, add_zero, coin_true]`.
:::
:::solution
```
rw [bind_true, Bool.cond_true, Bool.cond_false]
rw [pure_true, Bool.cond_false, mul_zero, add_zero, coin_true]
```
:::
::::

::::circuit (inputs := "x y") (gates := "and, or, not") (coins := "p 1|0") (target := "bernoulli p") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← (bif x then pure true else pure false); pure y) true = (↑p : ENNReal)") (new := "mul_one") (play := "x>y.0; y>out")
:::en
*Copying.* `y` is surely `true` after `true`, and surely `false` after `false`: it copies `x`. The
output `y` has the distribution of the coin `x`.
:::

:::de
*Abschreiben.* `y` ist sicher `true` nach `true` und sicher `false` nach `false`: Es schreibt `x` ab.
Der Ausgang `y` hat die Verteilung der Münze `x`.
:::

:::proofen
As before; now both ways end in a point mass. New: `mul_one : a * 1 = a`.

*Tip.* `rw [bind_true, Bool.cond_true, Bool.cond_false]`, then
`rw [pure_true, pure_true, Bool.cond_true, Bool.cond_false, mul_one, mul_zero, add_zero, coin_true]`.
:::

:::proofde
Wie eben; jetzt enden beide Wege in einer Punktmasse. Neu: `mul_one : a * 1 = a`.

*Tipp.* `rw [bind_true, Bool.cond_true, Bool.cond_false]`, dann
`rw [pure_true, pure_true, Bool.cond_true, Bool.cond_false, mul_one, mul_zero, add_zero, coin_true]`.
:::
:::solution
```
rw [bind_true, Bool.cond_true, Bool.cond_false]
rw [pure_true, pure_true, Bool.cond_true, Bool.cond_false, mul_one, mul_zero, add_zero, coin_true]
```
:::
::::

::::circuit (inputs := "x y") (gates := "and, or, not") (coins := "p 1|p") (target := "bool true:2p-p^2 false:(1-p)^2") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← (bif x then pure true else coin p); pure y) true = (↑p + ↑(σ p) * ↑p : ENNReal)") (play := "x>y.0; y>out")
:::en
*One more try.* When `x` showed `true`, that is enough: `y` is surely `true`. When it showed `false`,
throw again. Compare with *At least one `true`* of *Building with Coins*: the same as `x || y`, but the
second coin is only thrown when it is needed.
:::

:::de
*Noch ein Versuch.* Zeigte `x` `true`, reicht das: `y` ist sicher `true`. Zeigte es `false`, wirf noch
einmal. Vergleiche mit *Mindestens einmal `true`* aus *Bauen mit Münzen*: dasselbe wie `x || y`, aber die
zweite Münze wird nur geworfen, wenn sie gebraucht wird.
:::

:::proofen
The way through `true` has mass $`p \cdot 1`, the way through `false` mass $`(1 - p) \cdot p`.

*Tip.* `rw [bind_true, Bool.cond_true, Bool.cond_false]`, then
`rw [pure_true, Bool.cond_true, mul_one, coin_true, coin_false]`.
:::

:::proofde
Der Weg über `true` hat die Masse $`p \cdot 1`, der Weg über `false` die Masse $`(1 - p) \cdot p`.

*Tipp.* `rw [bind_true, Bool.cond_true, Bool.cond_false]`, dann
`rw [pure_true, Bool.cond_true, mul_one, coin_true, coin_false]`.
:::
:::solution
```
rw [bind_true, Bool.cond_true, Bool.cond_false]
rw [pure_true, Bool.cond_true, mul_one, coin_true, coin_false]
```
:::
::::

::::circuit (inputs := "x y") (gates := "and, or, not") (coins := "p p|1-p") (target := "bool true:1-2p+2p^2 false:2p-2p^2") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← (bif x then coin p else coin (σ p)); pure y) true = (↑p * ↑p + ↑(σ p) * ↑(σ p) : ENNReal)") (play := "x>y.0; y>out")
:::en
*A coin that remembers.* After `true` the coin `p` again, after `false` the flipped coin $`1 - p`:
the second throw tends to repeat the first.
:::

:::de
*Eine Münze, die sich erinnert.* Nach `true` wieder die Münze `p`, nach `false` die umgedrehte Münze
$`1 - p`: Der zweite Wurf wiederholt eher den ersten.
:::

:::proofen
Two coins in the two ways now, and `coin_true` is needed twice: `rw` rewrites one form at a time, here
first `(coin p) true` (everywhere), then `(coin (σ p)) true`.

*Tip.* `rw [bind_true, Bool.cond_true, Bool.cond_false]`, then `rw [coin_true, coin_true, coin_false]`.
:::

:::proofde
Jetzt zwei Münzen in den zwei Wegen, und `coin_true` wird zweimal gebraucht: `rw` schreibt eine Form
nach der anderen um, hier erst `(coin p) true` (überall), dann `(coin (σ p)) true`.

*Tipp.* `rw [bind_true, Bool.cond_true, Bool.cond_false]`, dann `rw [coin_true, coin_true, coin_false]`.
:::
:::solution
```
rw [bind_true, Bool.cond_true, Bool.cond_false]
rw [coin_true, coin_true, coin_false]
```
:::
::::

::::circuit (inputs := "x y z") (gates := "and, or, not") (coins := "p 1|p 1|p") (target := "bool true:3p-3p^2+p^3 false:(1-p)^3") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← (bif x then pure true else coin p); let z ← (bif y then pure true else coin p); pure z) true = (↑p + ↑(σ p) * (↑p + ↑(σ p) * ↑p) : ENNReal)") (play := "x>y.0; y>z.0; z>out")
:::en
*Boss: three tries.* Throw until `true` comes, at most three times. `y` waits for `x`, and `z` waits
for `y`. `false` only when all three tries fail: $`(1 - p)^3`.
:::

:::de
*Boss: drei Versuche.* Wirf, bis `true` kommt, höchstens dreimal. `y` wartet auf `x`, und `z` wartet auf
`y`. `false` nur, wenn alle drei Versuche scheitern: $`(1 - p)^3`.
:::

:::proofen
`bind_true` twice. After the first, the way through `true` is
`(do let y ← (bif true then pure true else coin p); …) true`: with `Bool.cond_true` it becomes
`(do let y ← pure true; …)`, and `pure_bind` (from *Draw, then Compute*) throws the point mass away:
`(bif true then pure true else coin p) true`. The way through `false` is a bind again: `bind_true`
once more.

*Tip.* `rw [bind_true, Bool.cond_true, Bool.cond_false, pure_bind, Bool.cond_true, pure_true, Bool.cond_true, mul_one]`,
then `rw [bind_true, Bool.cond_true, Bool.cond_false, pure_true, Bool.cond_true, mul_one]`, then
`rw [coin_true, coin_false]`.
:::

:::proofde
Zweimal `bind_true`. Nach dem ersten ist der Weg über `true`
`(do let y ← (bif true then pure true else coin p); …) true`: Mit `Bool.cond_true` wird daraus
`(do let y ← pure true; …)`, und `pure_bind` (aus *Erst ziehen, dann rechnen*) wirft die Punktmasse weg:
`(bif true then pure true else coin p) true`. Der Weg über `false` ist wieder ein bind: noch einmal
`bind_true`.

*Tipp.* `rw [bind_true, Bool.cond_true, Bool.cond_false, pure_bind, Bool.cond_true, pure_true, Bool.cond_true, mul_one]`,
dann `rw [bind_true, Bool.cond_true, Bool.cond_false, pure_true, Bool.cond_true, mul_one]`, dann
`rw [coin_true, coin_false]`.
:::
:::solution
```
rw [bind_true, Bool.cond_true, Bool.cond_false, pure_bind, Bool.cond_true, pure_true, Bool.cond_true, mul_one]
rw [bind_true, Bool.cond_true, Bool.cond_false, pure_true, Bool.cond_true, mul_one]
rw [coin_true, coin_false]
```
:::
::::
