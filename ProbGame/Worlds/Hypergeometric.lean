import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Hypergeometric" =>

%%%
htmlSplit := .never
%%%

:::en
An urn with white and black balls; balls are drawn one after the other, without putting them back. The hypergeometric distribution, the number of white balls drawn, as a `do` block that draws ball by ball: each draw is a stage (as in *Multi-Stage Experiments*), its chance depending on what was drawn before. At the end, a balance (as in *Balance*): the second ball. In Lean only.
:::

:::de
Eine Urne mit weißen und schwarzen Kugeln; Kugeln werden eine nach der anderen gezogen, ohne sie zurückzulegen. Die hypergeometrische Verteilung, die Anzahl der gezogenen weißen Kugeln, als `do`-Block, der Kugel für Kugel zieht: Jeder Zug ist eine Stufe (wie in *Mehrstufige Experimente*), ihre Chance hängt davon ab, was vorher gezogen wurde. Am Ende ein Gleichgewicht (wie in *Gleichgewicht*): die zweite Kugel. Nur in Lean.
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
def hyper : ℕ → ℕ → ℕ → DiscreteMeasure ℕ
  | _, _, 0 => pure 0
  | w, b, n + 1 => do
      let X ← coin (frac w b)
      bif X then (do let Y ← hyper … n; pure (1 + Y))
        else hyper w (b - 1) n
```

`frac w b` is $`w / (w + b)`, the chance of a white ball. (The urn after a white ball is left open: the next level asks for it.)

The first case of the definition.
:::

:::proofde
Kugel für Kugel gezogen, als `do`-Block:

```
def hyper : ℕ → ℕ → ℕ → DiscreteMeasure ℕ
  | _, _, 0 => pure 0
  | w, b, n + 1 => do
      let X ← coin (frac w b)
      bif X then (do let Y ← hyper … n; pure (1 + Y))
        else hyper w (b - 1) n
```

`frac w b` ist $`w / (w + b)`, die Chance auf eine weiße Kugel. (Die Urne nach einer weißen Kugel bleibt offen: Das nächste Level fragt danach.)

Der erste Fall der Definition.
:::
:::solution
```
rfl
```
:::
::::

::::leanonly (proof := "(w b n : ℕ) : hyper w b (n + 1) = (do let X ← coin (frac w b); bif X then (do let Y ← hyper ⟦w - 1 ‖ w, w - 1, w + 1⟧ ⟦b ‖ b - 1, b, b + 1⟧ n; pure (1 + Y)) else hyper w (b - 1) n)") (lemma := "hyper_succ") (group := "chance.count") (uses := "-")
:::en
*One ball after the other.* The first ball is white with chance $`w / (w + b)`, and then one more is counted. From which urn are the other $`n` balls drawn then: how many white, how many black? (After a black ball: one black less.)
:::

:::de
*Eine Kugel nach der anderen.* Die erste Kugel ist weiß mit Chance $`w / (w + b)`, und dann wird eins mehr gezählt. Aus welcher Urne werden dann die anderen $`n` Kugeln gezogen: wie viele weiße, wie viele schwarze? (Nach einer schwarzen Kugel: eine schwarze weniger.)
:::

:::proofen
The second case of the definition.
:::

:::proofde
Der zweite Fall der Definition.
:::
:::solution
```
rfl
```
:::
::::

:::::leanonly (proof := "(w b : ℕ) : hyper w b 1 1 = ⟦↑(frac w b) ‖ ↑(σ (frac w b)), ↑(frac w b), ↑(frac b w), 1⟧") (lemma := "hyper_one_one") (group := "chance.count") (uses := "hyper_succ, hyper_zero")
::::hint (anchor := "gap")
:::en
One ball drawn: with which chance is it white?
:::

:::de
Eine Kugel gezogen: Mit welcher Chance ist sie weiß?
:::
::::

:::en
*One draw, white.* One ball drawn, and the number of white ones is $`1`.
:::

:::de
*Ein Zug, weiß.* Eine Kugel gezogen, und die Anzahl der weißen ist $`1`.
:::

:::proofen
`hyper_succ` writes the draw out; the rest is computing, as in *Binomial*, with `hyper_zero` for the
draws that are left. Your result becomes the lemma `hyper_one_one`.
:::

:::proofde
`hyper_succ` schreibt den Zug aus; der Rest ist Rechnen, wie in *Binomial*, mit `hyper_zero` für die
Züge, die übrig sind. Dein Ergebnis wird das Lemma `hyper_one_one`.
:::
:::solution
```
rw [hyper_succ]
simp [hyper_zero]
```
:::
:::::

:::::leanonly (proof := "(w b : ℕ) : hyper w b 1 0 = ⟦↑(σ (frac w b)) ‖ ↑(frac w b), 0, ↑(σ (frac w b)), ↑(frac w (b - 1))⟧") (lemma := "hyper_one_zero") (new := "pure_one_zero") (group := "chance.count") (uses := "hyper_succ, hyper_zero, pure_one_zero")
::::hint (anchor := "gap")
:::en
One ball drawn: with which chance is it not white?
:::

:::de
Eine Kugel gezogen: Mit welcher Chance ist sie nicht weiß?
:::
::::

:::en
*One draw, black.* One ball drawn, and the number of white ones is $`0`.
:::

:::de
*Ein Zug, schwarz.* Eine Kugel gezogen, und die Anzahl der weißen ist $`0`.
:::

:::proofen
As in the level before. After a white ball the count is surely $`1`, and not $`0`: the new rule `pure_one_zero : (pure 1) 0 = 0`, given to `simp` by hand. Your result becomes the lemma `hyper_one_zero`.
:::

:::proofde
Wie im Level davor. Nach einer weißen Kugel ist die Anzahl sicher $`1`, und nicht $`0`: die neue Regel `pure_one_zero : (pure 1) 0 = 0`, `simp` von Hand mitgegeben. Dein Ergebnis wird das Lemma `hyper_one_zero`.
:::
:::solution
```
rw [hyper_succ]
simp [hyper_zero, pure_one_zero]
```
:::
:::::

:::::leanonly (proof := "(w b : ℕ) : hyper w b 2 1 = (⟦↑(frac w b) * ↑(σ (frac (w - 1) b)) + ↑(σ (frac w b)) * ↑(frac w (b - 1)) ‖ ↑(frac w b) * ↑(σ (frac w b)) + ↑(σ (frac w b)) * ↑(frac w b), ↑(frac w b) * ↑(σ (frac (w - 1) b)) + ↑(σ (frac w b)) * ↑(frac w (b - 1)), ↑(frac w b) * ↑(σ (frac (w - 1) b))⟧ : ℝ≥0∞)") (group := "chance.count") (uses := "hyper_succ, hyper_one_zero, hyper_one_one, hyper_zero")
::::hint (anchor := "gap")
:::en
White and then black, or black and then white. The second ball comes from another urn than the first.
:::

:::de
Weiß und dann schwarz, oder schwarz und dann weiß. Die zweite Kugel kommt aus einer anderen Urne als die erste.
:::
::::

:::en
*One of each.* Two draws, exactly one white ball: the first mass of the hypergeometric distribution with both colours in it.
:::

:::de
*Eine von jeder.* Zwei Züge, genau eine weiße Kugel: die erste Masse der hypergeometrischen Verteilung, in der beide Farben vorkommen.
:::

:::proofen
The first draw as before. The second draws are your two lemmas, for the smaller urns.
:::

:::proofde
Der erste Zug wie eben. Die zweiten Züge sind deine zwei Lemmas, für die kleineren Urnen.
:::
:::solution
```
rw [hyper_succ]
simp [hyper_one_zero, hyper_one_one]
```
:::
:::::

::::leanonly (proof := "(b : ℕ) : coin (frac 0 b) = pure false") (new := "frac_zero") (group := "chance.count") (uses := "frac_zero, coin_zero, frac_white, coin_one")
:::en
*No white ball.* Without white balls, the ball drawn is surely black.
:::

:::de
*Keine weiße Kugel.* Ohne weiße Kugeln ist die gezogene Kugel sicher schwarz.
:::

:::proofen
`frac_zero : frac 0 b = 0`, and `coin_zero : coin 0 = pure false` from *Counting*.
:::

:::proofde
`frac_zero : frac 0 b = 0`, und `coin_zero : coin 0 = pure false` aus *Zählen*.
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
:::

:::proofde
Induktion über $`n`, für jedes $`b` (die Urne wird kleiner: `generalizing b`).
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
:::

:::proofde
`frac_white : frac (w + 1) 0 = 1` und `coin_one : coin 1 = pure true`.
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
:::

:::proofde
Induktion über $`w`. `Nat.add_sub_cancel : n + m - m = n` (eine weiße Kugel herausgenommen).
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
*Drawing all the balls.* Draw all $`w + b` balls, one after the other: whatever happens on the way, in the end you surely have all $`w` white ones.
:::

:::de
*Alle Kugeln ziehen.* Zieh alle $`w + b` Kugeln, eine nach der anderen: Was auch immer unterwegs passiert, am Ende hast du sicher alle $`w` weißen.
:::
:::proofen
Induction on $`w`, for every $`b`; in its step, an induction on $`b`. At the end both branches of the first draw are the same (`cond_same`, under the `do`: `simp only`), and the draw is not used (`coin_unused`).
:::

:::proofde
Induktion über $`w`, für jedes $`b`; in ihrem Schritt eine Induktion über $`b`. Am Ende sind beide Zweige des ersten Zugs gleich (`cond_same`, unter dem `do`: `simp only`), und der Zug wird nicht benutzt (`coin_unused`).
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

::::leanonly (proof := "(w b : ℕ) : 1 - ((frac (w + 1) b : I) : ℝ) = (b : ℝ) / ((w : ℝ) + 1 + b)") (new := "frac_real") (group := "chance.count") (uses := "frac_real, Nat.cast_add, Nat.cast_one")
:::en
*The share of black.* As in *Balance*, chances are compared as real numbers. One minus the share of white is the share of black. ($`w + 1` white balls: an empty urn has no shares.)
:::

:::de
*Der Anteil der schwarzen.* Wie in *Gleichgewicht* werden Chancen als reelle Zahlen verglichen. Eins minus der Anteil der weißen ist der Anteil der schwarzen. ($`w + 1` weiße Kugeln: Eine leere Urne hat keine Anteile.)
:::

:::proofen
`frac_real : ↑(frac w b) = ↑w / (↑w + ↑b)`, in `ℝ`; `Nat.cast_add` and `Nat.cast_one` write
`↑(w + 1)` as `↑w + 1`. Then an equation between fractions, as in *Balance*.
:::

:::proofde
`frac_real : ↑(frac w b) = ↑w / (↑w + ↑b)`, in `ℝ`; `Nat.cast_add` und `Nat.cast_one` schreiben
`↑(w + 1)` als `↑w + 1`. Dann eine Gleichung zwischen Brüchen, wie in *Gleichgewicht*.
:::
:::solution
```
rw [frac_real, Nat.cast_add, Nat.cast_one]
field_simp
ring
```
:::
::::

::::leanonly (proof := "(w b : ℕ) : (do let X ← coin (frac w b); bif X then coin (frac w b) else coin (frac w b)) = coin (frac w b)") (group := "chance.count") (uses := "coin_stays")
:::en
*Put back.* The first ball is drawn, looked at, and put back. Then the urn is the same after white and after black, and the second ball is white with the same chance as the first.
:::

:::de
*Zurückgelegt.* Die erste Kugel wird gezogen, angeschaut und zurückgelegt. Dann ist die Urne nach Weiß dieselbe wie nach Schwarz, und die zweite Kugel ist mit derselben Chance weiß wie die erste.
:::

:::proofen
A coin that stays: your lemma `coin_stays` from *Balance*. What it asks for is the balance, in `ℝ`.
:::

:::proofde
Eine Münze, die bleibt: dein Lemma `coin_stays` aus *Gleichgewicht*. Was es verlangt, ist das
Gleichgewicht, in `ℝ`.
:::
:::solution
```
apply coin_stays
ring
```
:::
::::

:::::leanonly (proof := "(x y : ℝ) (h : x + y = 1) : x * y + y * x = ⟦2 * x * (1 - x) ‖ x * (1 - x), 2 * x * (1 - x), 1 - x * x⟧") (group := "chance.count") (uses := "-")
::::hint (anchor := "gap")
:::en
White then black, or black then white; and $`y` is $`1 - x`.
:::

:::de
Erst Weiß, dann Schwarz, oder erst Schwarz, dann Weiß; und $`y` ist $`1 - x`.
:::
::::

:::en
*Put back: two colours.* Two draws, the first ball put back. $`x` is the share of white, $`y` the share of black (`h`: there are no other balls). The chance of two different colours, in $`x` alone?
:::

:::de
*Zurückgelegt: zwei Farben.* Zwei Züge, die erste Kugel zurückgelegt. $`x` ist der Anteil der weißen, $`y` der Anteil der schwarzen (`h`: Andere Kugeln gibt es nicht). Die Chance auf zwei verschiedene Farben, nur in $`x`?
:::

:::proofen
A hypothesis and a computation: `linear_combination`, from *Balance*. This time the factor in front
of `h` is not a number.
:::

:::proofde
Eine Annahme und eine Rechnung: `linear_combination`, aus *Gleichgewicht*. Diesmal ist der Faktor
vor `h` keine Zahl.
:::
:::solution
```
linear_combination 2 * x * h
```
:::
:::::

::::leanonly (proof := "(w b : ℕ) : (do let X ← coin (frac (w + 1) (b + 1)); bif X then coin (frac w (b + 1)) else coin (frac (w + 1) b)) = coin (⟦frac (w + 1) (b + 1) ‖ frac w (b + 1), frac (w + 1) b, frac (w + 1) (b + 1), frac w b⟧)") (group := "chance.count") (uses := "coin_stays, frac_real")
:::en
*Boss: the second ball.* An urn with $`w + 1` white and $`b + 1` black balls. The first ball is drawn and put aside, unseen. The second ball: white with which chance?
:::

:::de
*Endgegner: die zweite Kugel.* Eine Urne mit $`w + 1` weißen und $`b + 1` schwarzen Kugeln. Die erste Kugel wird gezogen und beiseitegelegt, ungesehen. Die zweite Kugel: mit welcher Chance weiß?
:::
:::solution
```
apply coin_stays
rw [frac_real, frac_real, frac_real]
simp
field_simp
ring
```
:::
::::
