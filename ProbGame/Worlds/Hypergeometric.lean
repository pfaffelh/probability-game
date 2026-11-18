import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Hypergeometric" =>

%%%
htmlSplit := .never
%%%

:::en
An urn with white and black balls; balls are drawn one after the other, without putting them back. The hypergeometric distribution, the number of white balls drawn, as a `do` block that draws ball by ball: each draw is a coin that waits (as in *Coins that Wait*), its chance depending on what was drawn before. In Lean only.
:::

:::de
Eine Urne mit weißen und schwarzen Kugeln; Kugeln werden eine nach der anderen gezogen, ohne sie zurückzulegen. Die hypergeometrische Verteilung, die Anzahl der gezogenen weißen Kugeln, als `do`-Block, der Kugel für Kugel zieht: Jeder Zug ist eine Münze, die wartet (wie in *Münzen, die warten*), ihre Chance hängt davon ab, was vorher gezogen wurde. Nur in Lean.
:::

::::leanonly (proof := "(w b : ℕ) : hyper w b 0 = pure 0") (lemma := "hyper_zero") (group := "chance.count") (uses := "-")
:::en
*No draw.* An urn with $`w` white and $`b` black balls. `hyper w b n` is the number of white balls in $`n` draws, one after the other, without putting a ball back. With no draw: none.
:::

:::de
*Kein Zug.* Eine Urne mit $`w` weißen und $`b` schwarzen Kugeln. `hyper w b n` ist die Anzahl der weißen Kugeln in $`n` Zügen, einer nach dem anderen, ohne eine Kugel zurückzulegen. Ohne Zug: keine.
:::

:::proofen
Drawn ball by ball, as a `do` block:

```
def hyper : ℕ → ℕ → ℕ → PMF ℕ
  | _, _, 0 => pure 0
  | w, b, n + 1 => do
      let X ← coin (frac w b)
      bif X then (do let Y ← hyper (w - 1) b n; pure (1 + Y))
        else hyper w (b - 1) n
```

`frac w b` is $`w / (w + b)`, the chance of a white ball.

The first case of the definition.

*Tip.* `rfl`.
:::

:::proofde
Kugel für Kugel gezogen, als `do`-Block:

```
def hyper : ℕ → ℕ → ℕ → PMF ℕ
  | _, _, 0 => pure 0
  | w, b, n + 1 => do
      let X ← coin (frac w b)
      bif X then (do let Y ← hyper (w - 1) b n; pure (1 + Y))
        else hyper w (b - 1) n
```

`frac w b` ist $`w / (w + b)`, die Chance auf eine weiße Kugel.

Der erste Fall der Definition.

*Tipp.* `rfl`.
:::
:::solution
```
rfl
```
:::
::::

::::leanonly (proof := "(w b n : ℕ) : hyper w b (n + 1) = (do let X ← coin (frac w b); bif X then (do let Y ← hyper (w - 1) b n; pure (1 + Y)) else hyper w (b - 1) n)") (lemma := "hyper_succ") (group := "chance.count") (uses := "-")
:::en
*One ball after the other.* The first ball is white with chance $`w / (w + b)`: then one white less in the urn, and one more counted. Else one black less.
:::

:::de
*Eine Kugel nach der anderen.* Die erste Kugel ist weiß mit Chance $`w / (w + b)`: dann eine weiße weniger in der Urne, und eins mehr gezählt. Sonst eine schwarze weniger.
:::

:::proofen
The second case of the definition.

*Tip.* `rfl`.
:::

:::proofde
Der zweite Fall der Definition.

*Tipp.* `rfl`.
:::
:::solution
```
rfl
```
:::
::::

::::leanonly (proof := "(b : ℕ) : coin (frac 0 b) = pure false") (new := "frac_zero, coin_zero") (group := "chance.count") (uses := "frac_zero, coin_zero, frac_white, coin_one")
:::en
*No white ball.* Without white balls, the ball drawn is surely black.
:::

:::de
*Keine weiße Kugel.* Ohne weiße Kugeln ist die gezogene Kugel sicher schwarz.
:::

:::proofen
`frac_zero : frac 0 b = 0` and `coin_zero : coin 0 = pure false`.

*Tip.* `rw [frac_zero, coin_zero]`.
:::

:::proofde
`frac_zero : frac 0 b = 0` und `coin_zero : coin 0 = pure false`.

*Tipp.* `rw [frac_zero, coin_zero]`.
:::
:::solution
```
rw [frac_zero, coin_zero]
```
:::
::::

::::leanonly (proof := "(b n : ℕ) : hyper 0 b n = pure 0") (lemma := "hyper_black") (group := "chance.count") (uses := "hyper_zero, hyper_succ, frac_zero, coin_zero, pure_bind, Bool.cond_false, frac_white, coin_one, bind_pure, Bool.cond_true")
:::en
*Only black.* From an urn without white balls, no white one is ever drawn.
:::

:::de
*Nur schwarze.* Aus einer Urne ohne weiße Kugeln wird nie eine weiße gezogen.
:::

:::proofen
Induction on $`n`, for every $`b` (the urn gets smaller: `generalizing b`).

*Tip.* `induction' n with n ih generalizing b`; `rw [hyper_zero]`; `rw [hyper_succ, frac_zero, coin_zero, pure_bind, Bool.cond_false, ih]`.
:::

:::proofde
Induktion über $`n`, für jedes $`b` (die Urne wird kleiner: `generalizing b`).

*Tipp.* `induction' n with n ih generalizing b`; `rw [hyper_zero]`; `rw [hyper_succ, frac_zero, coin_zero, pure_bind, Bool.cond_false, ih]`.
:::
:::solution
```
induction' n with n ih generalizing b
rw [hyper_zero]
rw [hyper_succ, frac_zero, coin_zero, pure_bind, Bool.cond_false, ih]
```
:::
::::

::::leanonly (proof := "(w : ℕ) : coin (frac (w + 1) 0) = pure true") (new := "frac_white, coin_one") (group := "chance.count") (uses := "frac_white, coin_one, frac_zero, coin_zero")
:::en
*No black ball.* Without black balls (and with at least one white one), the ball drawn is surely white.
:::

:::de
*Keine schwarze Kugel.* Ohne schwarze Kugeln (und mit mindestens einer weißen) ist die gezogene Kugel sicher weiß.
:::

:::proofen
`frac_white : frac (w + 1) 0 = 1` and `coin_one : coin 1 = pure true`.

*Tip.* `rw [frac_white, coin_one]`.
:::

:::proofde
`frac_white : frac (w + 1) 0 = 1` und `coin_one : coin 1 = pure true`.

*Tipp.* `rw [frac_white, coin_one]`.
:::
:::solution
```
rw [frac_white, coin_one]
```
:::
::::

::::leanonly (proof := "(w : ℕ) : hyper w 0 w = pure w") (lemma := "hyper_white") (new := "Nat.add_sub_cancel") (group := "chance.count") (uses := "hyper_zero, hyper_succ, frac_white, coin_one, pure_bind, Bool.cond_true, Nat.add_sub_cancel, add_comm, frac_zero, coin_zero, bind_pure, Bool.cond_false, add_assoc")
:::en
*Only white.* $`w` draws from an urn with $`w` white balls: all of them, surely.
:::

:::de
*Nur weiße.* $`w` Züge aus einer Urne mit $`w` weißen Kugeln: alle, sicher.
:::

:::proofen
Induction on $`w`. `Nat.add_sub_cancel : n + m - m = n` (one white ball taken out).

*Tip.* `induction' w with w ih`; `rw [hyper_zero]`; `rw [hyper_succ, frac_white, coin_one, pure_bind, Bool.cond_true, Nat.add_sub_cancel, ih, pure_bind, add_comm]`.
:::

:::proofde
Induktion über $`w`. `Nat.add_sub_cancel : n + m - m = n` (eine weiße Kugel herausgenommen).

*Tipp.* `induction' w with w ih`; `rw [hyper_zero]`; `rw [hyper_succ, frac_white, coin_one, pure_bind, Bool.cond_true, Nat.add_sub_cancel, ih, pure_bind, add_comm]`.
:::
:::solution
```
induction' w with w ih
rw [hyper_zero]
rw [hyper_succ, frac_white, coin_one, pure_bind, Bool.cond_true, Nat.add_sub_cancel, ih, pure_bind, add_comm]
```
:::
::::

::::leanonly (proof := "(w b : ℕ) : hyper w b (w + b) = pure w") (lemma := "hyper_all") (group := "chance.count") (uses := "zero_add, hyper_black, add_zero, hyper_white, add_assoc, hyper_succ, Nat.add_sub_cancel, add_right_comm, pure_bind, add_comm, cond_same, coin_unused, mul_zero, hyper_zero, bind_pure, prob_unused")
:::en
*Boss: drawing all the balls.* Draw all $`w + b` balls, one after the other: whatever happens on the way, in the end you surely have all $`w` white ones.
:::

:::de
*Endgegner: alle Kugeln ziehen.* Zieh alle $`w + b` Kugeln, eine nach der anderen: Was auch immer unterwegs passiert, am Ende hast du sicher alle $`w` weißen.
:::

:::proofen
A double induction, as for the binomial formula: on $`w` for every $`b`, and inside on $`b`. With $`w = 0` it is `hyper_black`, with $`b = 0` `hyper_white`. In the step, the first ball: white leaves an urn with $`w` white and $`b + 1` black (outer `ih`), black one with $`w + 1` and $`b` (inner `ih2`). Both branches give `pure (w + 1)`: then the coin does not matter (`cond_same` under the `do`, with `simp only`, and `coin_unused`).

*Tip.* `induction' w with w ih generalizing b`; `rw [zero_add, hyper_black]`; `induction' b with b ih2`; `rw [add_zero, hyper_white]`; `rw [← add_assoc, hyper_succ, Nat.add_sub_cancel, Nat.add_sub_cancel, ih2, add_right_comm, add_assoc, ih, pure_bind, add_comm 1 w]`, `simp only [cond_same]`, `rw [coin_unused]`.
:::

:::proofde
Eine doppelte Induktion, wie bei der Binomialformel: über $`w` für jedes $`b`, und darin über $`b`. Mit $`w = 0` ist es `hyper_black`, mit $`b = 0` `hyper_white`. Im Schritt die erste Kugel: Weiß lässt eine Urne mit $`w` weißen und $`b + 1` schwarzen (äußeres `ih`), schwarz eine mit $`w + 1` und $`b` (inneres `ih2`). Beide Zweige geben `pure (w + 1)`: Dann spielt die Münze keine Rolle (`cond_same` unter dem `do`, mit `simp only`, und `coin_unused`).

*Tipp.* `induction' w with w ih generalizing b`; `rw [zero_add, hyper_black]`; `induction' b with b ih2`; `rw [add_zero, hyper_white]`; `rw [← add_assoc, hyper_succ, Nat.add_sub_cancel, Nat.add_sub_cancel, ih2, add_right_comm, add_assoc, ih, pure_bind, add_comm 1 w]`, `simp only [cond_same]`, `rw [coin_unused]`.
:::
:::solution
```
induction' w with w ih generalizing b
rw [zero_add, hyper_black]
induction' b with b ih2
rw [add_zero, hyper_white]
rw [← add_assoc, hyper_succ, Nat.add_sub_cancel, Nat.add_sub_cancel, ih2, add_right_comm, add_assoc, ih, pure_bind, add_comm 1 w]
simp only [cond_same]
rw [coin_unused]
```
:::
::::
