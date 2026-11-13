import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Circuits with Coins" =>

%%%
htmlSplit := .never
%%%

:::en
The circuits of the world *Circuits*, now with a coin `coin p` at each input, thrown independently.
The output is then random too: its distribution is the target. Each row of the truth table has a
mass, the product of the masses of its inputs (`p` for `true`, `1 − p` for `false`), and the mass of
the output at `true` is the sum over the rows where the output is `true`. Two coins joined by `and`
are again a coin: `true` with probability `p · p`.
:::

:::de
Die Schaltungen der Welt *Schaltungen*, jetzt mit einer Münze `coin p` an jedem Eingang, unabhängig
geworfen. Dann ist auch der Ausgang zufällig: Seine Verteilung ist das Ziel. Jede Zeile der
Wahrheitstafel hat eine Masse, das Produkt der Massen ihrer Eingänge (`p` für `true`, `1 − p` für
`false`), und die Masse des Ausgangs bei `true` ist die Summe über die Zeilen, in denen der Ausgang
`true` ist. Zwei Münzen, mit `und` verknüpft, sind wieder eine Münze: `true` mit Wahrscheinlichkeit
`p · p`.
:::

::::circuit (inputs := "x y") (gates := "and, or, not") (coins := "p p") (target := "bool true:p^2 false:1-p^2") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure (x && y)) = coin (p * p)") (play := "a=and; x>a.0; y>a.1; a>out")
:::en
*Two coins, one coin.* `true` with probability `p²`.
:::

:::de
*Zwei Münzen, eine Münze.* `true` mit Wahrscheinlichkeit `p²`.
:::

:::proofen
Independence, as a rule: `coin_and`.

*Tip.* `rw [coin_and]`.
:::

:::proofde
Unabhängigkeit, als Regel: `coin_and`.

*Tipp.* `rw [coin_and]`.
:::
:::solution
```
rw [coin_and]
```
:::
::::

::::circuit (inputs := "x y") (gates := "and, or, not") (coins := "p p") (target := "bool true:p(1-p) false:1-p(1-p)") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure (x && !y)) = coin (p * σ p)") (play := "a=not; b=and; y>a.0; x>b.0; a>b.1; b>out")
:::en
*First true, then false.* `true` with probability `p (1 − p)`.
:::

:::de
*Erst true, dann false.* `true` mit Wahrscheinlichkeit `p (1 − p)`.
:::

:::proofen
*Tip.* `rw [← coin_and]`, `rw [← coin_not]`, `simp only [bind_map_left]`.
:::

:::proofde
*Tipp.* `rw [← coin_and]`, `rw [← coin_not]`, `simp only [bind_map_left]`.
:::
:::solution
```
rw [← coin_and]
rw [← coin_not]
simp only [bind_map_left]
```
:::
::::

::::circuit (inputs := "x y") (gates := "and, or, not") (coins := "p p") (target := "bool true:2p-p^2 false:(1-p)^2") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure (x || y)) = coin (σ (σ p * σ p))") (play := "a=or; x>a.0; y>a.1; a>out")
:::en
*At least one.* `false` only when both are: with probability `(1 − p)²`.
:::

:::de
*Mindestens eine.* `false` nur, wenn beide es sind: mit Wahrscheinlichkeit `(1 − p)²`.
:::

:::proofen
*Tip.* `rw [← coin_not]`, `rw [← coin_and]`, `rw [← coin_not]`,
`simp only [bind_map_left, map_bind, map_pure, or_eq]`.
:::

:::proofde
*Tipp.* `rw [← coin_not]`, `rw [← coin_and]`, `rw [← coin_not]`,
`simp only [bind_map_left, map_bind, map_pure, or_eq]`.
:::
:::solution
```
rw [← coin_not]
rw [← coin_and]
rw [← coin_not]
simp only [bind_map_left, map_bind, map_pure, or_eq]
```
:::
::::

::::circuit (inputs := "x y") (gates := "and, or, not") (coins := "p p") (target := "bool true:2p(1-p) false:p^2+(1-p)^2") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure ((x || y) && !(x && y))) = (do let x ← coin p; let y ← coin p; pure (xor x y))") (play := "a=or; b=and; c=not; d=and; x>a.0; y>a.1; x>b.0; y>b.1; b>c.0; a>d.0; c>d.1; d>out")
:::en
*Exactly one.* Your circuit of *Circuits*, with coins: the rows `ft` and `tf`, each with mass
`p (1 − p)`.
:::

:::de
*Genau eine.* Deine Schaltung aus *Schaltungen*, mit Münzen: die Zeilen `ft` und `tf`, jede mit Masse
`p (1 − p)`.
:::

:::proofen
Both sides throw the same coins; go under the throws, and look at the four rows.

*Tip.* `congr 1`, `funext x`, `congr 1`, `funext y`, `cases x <;> cases y <;> rfl`.
:::

:::proofde
Beide Seiten werfen dieselben Münzen; geh unter die Würfe und sieh dir die vier Zeilen an.

*Tipp.* `congr 1`, `funext x`, `congr 1`, `funext y`, `cases x <;> cases y <;> rfl`.
:::
:::solution
```
congr 1
funext x
congr 1
funext y
cases x <;> cases y <;> rfl
```
:::
::::

::::circuit (inputs := "x y z") (gates := "and, or") (coins := "p p p") (target := "bool true:3p^2-2p^3 false:1-3p^2+2p^3") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; let z ← coin p; pure ((x && y) || (x && z) || (y && z))) = (fun n => decide (2 ≤ n)) <$> binom p 3") (play := "a=and; b=and; c=and; d=or; e=or; x>a.0; y>a.1; x>b.0; z>b.1; y>c.0; z>c.1; a>d.0; b>d.1; d>e.0; c>e.1; e>out")
:::en
*The boss: the majority of three coins.* Your circuit of the boss of *Circuits*, with three coins.
:::

:::de
*Der Endgegner: die Mehrheit von drei Münzen.* Deine Schaltung aus dem Endgegner von *Schaltungen*,
mit drei Münzen.
:::

:::proofen
*Tip.* Unfold `binom p 3` with `binom_succ` (three times) and `binom_zero`; clean up with
`simp only [map_bind, bind_assoc, pure_bind, map_pure, add_zero]`; then go under the three throws
and look at all eight rows.
:::

:::proofde
*Tipp.* Wickle `binom p 3` mit `binom_succ` (dreimal) und `binom_zero` aus; räume auf mit
`simp only [map_bind, bind_assoc, pure_bind, map_pure, add_zero]`; dann geh unter die drei Würfe und
sieh dir alle acht Zeilen an.
:::
:::solution
```
rw [binom_succ, binom_succ, binom_succ, binom_zero]
simp only [map_bind, bind_assoc, pure_bind, map_pure, add_zero]
congr 1
funext x
congr 1
funext y
congr 1
funext z
cases x <;> cases y <;> cases z <;> rfl
```
:::
::::
