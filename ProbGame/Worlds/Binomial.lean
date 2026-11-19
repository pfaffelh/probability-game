import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Binomial" =>

%%%
htmlSplit := .never
%%%

:::en
`binom p n` is the number of `true` in $`n` throws of a coin `p`, defined by recursion on $`n` (in *Counting*). Here its masses: by induction, Pascal's triangle with masses, up to the binomial formula.
:::

:::de
`binom p n` ist die Anzahl der `true` in $`n` Würfen einer Münze `p`, durch Rekursion über $`n` definiert (in *Zählen*). Hier ihre Massen: durch Induktion, das Pascalsche Dreieck mit Massen, bis zur Binomialformel.
:::

::::leanonly (proof := "{β : Type} (p : I) (f : Bool → DiscreteMeasure β) (x : β) : (do let b ← coin p; f b) x = ↑p * f true x + ↑(σ p) * f false x") (lemma := "coin_bind_apply") (group := "chance.count") (uses := "bind_apply, Fintype.sum_bool, coin_true, coin_false, coin_total")
:::en
*A coin first.* A draw that starts with a coin `p`: the mass at any point `x` comes through `true`
(mass $`p`) and through `false` (mass $`1 - p`). That is `bind_true` again, now at any point.
:::

:::de
*Erst eine Münze.* Ein Ziehen, das mit einer Münze `p` beginnt: Die Masse an jedem Punkt `x` kommt
über `true` (Masse $`p`) und über `false` (Masse $`1 - p`). Das ist wieder `bind_true`, jetzt an jedem
Punkt.
:::

:::proofen
As for `bind_true`: `bind_apply : (do let a ← μ; f a) b = ∑ a, μ a * f a b` and the two summands of a sum over
`Bool`, then the masses of the coin. What you prove is unlocked as `coin_bind_apply`.

*Tip.* `rw [bind_apply, Fintype.sum_bool, coin_true, coin_false]`.
:::

:::proofde
Wie bei `bind_true`: `bind_apply : (do let a ← μ; f a) b = ∑ a, μ a * f a b` und die zwei Summanden einer
Summe über `Bool`, dann die Massen der Münze. Was du beweist, wird als `coin_bind_apply`
freigeschaltet.

*Tipp.* `rw [bind_apply, Fintype.sum_bool, coin_true, coin_false]`.
:::
:::solution
```
rw [bind_apply, Fintype.sum_bool, coin_true, coin_false]
```
:::
::::

::::leanonly (proof := "(p : I) (μ ν : DiscreteMeasure ℕ) (k : ℕ) : (do let x ← coin p; bif x then μ else ν) k = ↑p * μ k + ↑(σ p) * ν k") (group := "chance.count") (uses := "coin_bind_apply, Bool.cond_true, Bool.cond_false")
:::en
*Two branches.* After the coin, one of two distributions: `μ` after `true`, `ν` after `false`.
:::

:::de
*Zwei Zweige.* Nach der Münze eine von zwei Verteilungen: `μ` nach `true`, `ν` nach `false`.
:::

:::proofen
`coin_bind_apply : (do let b ← coin p; f b) x = ↑p * f true x + ↑(σ p) * f false x`, from the last level.

*Tip.* `rw [coin_bind_apply, Bool.cond_true, Bool.cond_false]`.
:::

:::proofde
`coin_bind_apply : (do let b ← coin p; f b) x = ↑p * f true x + ↑(σ p) * f false x`, aus dem letzten Level.

*Tipp.* `rw [coin_bind_apply, Bool.cond_true, Bool.cond_false]`.
:::
:::solution
```
rw [coin_bind_apply, Bool.cond_true, Bool.cond_false]
```
:::
::::

::::leanonly (proof := "{α : Type} [DecidableEq α] (a : α) : (pure a : DiscreteMeasure α) a = 1") (new := "beq_self_eq_true") (lemma := "pure_self") (group := "chance.count") (uses := "pure_apply, beq_self_eq_true, Bool.cond_true, Bool.cond_false")
:::en
*At its point.* A point mass has mass one at its point, now on any type.
:::

:::de
*An ihrem Punkt.* Eine Punktmasse hat an ihrem Punkt die Masse eins, jetzt auf jedem Typ.
:::

:::proofen
`pure_apply : (pure a) b = bif a == b then 1 else 0`, from *One Coin*; and
`beq_self_eq_true : (a == a) = true`. What you prove is unlocked as `pure_self`.

*Tip.* `rw [pure_apply, beq_self_eq_true, Bool.cond_true]`.
:::

:::proofde
`pure_apply : (pure a) b = bif a == b then 1 else 0`, aus *Eine Münze*; und
`beq_self_eq_true : (a == a) = true`. Was du beweist, wird als `pure_self` freigeschaltet.

*Tipp.* `rw [pure_apply, beq_self_eq_true, Bool.cond_true]`.
:::
:::solution
```
rw [pure_apply, beq_self_eq_true, Bool.cond_true]
```
:::
::::

::::leanonly (proof := "(p : I) : binom p 0 0 = 1") (group := "chance.count") (uses := "binom_zero, pure_self, binom_succ, pure_zero_succ")
:::en
*No throw.* With no throw, surely no `true`.
:::

:::de
*Kein Wurf.* Ohne Wurf sicher kein `true`.
:::

:::proofen
`pure_self : (pure a) a = 1`, from the last level.

*Tip.* `rw [binom_zero, pure_self]`.
:::

:::proofde
`pure_self : (pure a) a = 1`, aus dem letzten Level.

*Tipp.* `rw [binom_zero, pure_self]`.
:::
:::solution
```
rw [binom_zero, pure_self]
```
:::
::::

::::leanonly (proof := "(p : I) (k : ℕ) : binom p 0 (k + 1) = 0") (new := "pure_zero_succ") (group := "chance.count") (uses := "binom_zero, pure_zero_succ, binom_succ, pure_self")
:::en
*No throw, no true.* With no throw, a `true` is impossible.
:::

:::de
*Kein Wurf, kein true.* Ohne Wurf ist ein `true` unmöglich.
:::

:::proofen
`pure_zero_succ : (pure 0) (k + 1) = 0`.

*Tip.* `rw [binom_zero, pure_zero_succ]`.
:::

:::proofde
`pure_zero_succ : (pure 0) (k + 1) = 0`.

*Tipp.* `rw [binom_zero, pure_zero_succ]`.
:::
:::solution
```
rw [binom_zero, pure_zero_succ]
```
:::
::::

::::leanonly (proof := "(μ : DiscreteMeasure ℕ) (k : ℕ) : (do let Y ← μ; pure (1 + Y)) (k + 1) + (do let Y ← μ; pure (1 + Y)) 0 = μ k") (new := "shift_succ, shift_zero") (group := "chance.count") (uses := "shift_succ, shift_zero, add_zero, zero_add")
:::en
*One more.* Adding one to every outcome shifts the bars one place to the right: the mass at `k + 1` is the old mass at `k`, and at `0` there is nothing.
:::

:::de
*Eins mehr.* Eins zu jedem Ergebnis addieren schiebt die Säulen eine Stelle nach rechts: Die Masse bei `k + 1` ist die alte Masse bei `k`, und bei `0` ist nichts.
:::

:::proofen
`shift_succ : (do let Y ← μ; pure (1 + Y)) (k + 1) = μ k` and `shift_zero : (do let Y ← μ; pure (1 + Y)) 0 = 0`.

*Tip.* `rw [shift_succ, shift_zero, add_zero]`.
:::

:::proofde
`shift_succ : (do let Y ← μ; pure (1 + Y)) (k + 1) = μ k` und `shift_zero : (do let Y ← μ; pure (1 + Y)) 0 = 0`.

*Tipp.* `rw [shift_succ, shift_zero, add_zero]`.
:::
:::solution
```
rw [shift_succ, shift_zero, add_zero]
```
:::
::::

::::leanonly (proof := "(p : I) (n : ℕ) : binom p (n + 1) 0 = ↑(σ p) * binom p n 0") (lemma := "binom_succ_zero") (new := "Bool.toNat_false, mul_zero") (group := "chance.count") (uses := "binom_succ, coin_bind_apply, Bool.toNat_true, Bool.toNat_false, zero_add, bind_pure, shift_zero, mul_zero, binom_zero, add_zero, pure_bind, shift_succ")
:::en
*No true in one throw more.* No `true` in $`n + 1` throws: the first is `false`, and none in the other $`n`.
:::

:::de
*Kein true in einem Wurf mehr.* Kein `true` in $`n + 1` Würfen: Der erste ist `false`, und in den anderen $`n` keins.
:::

:::proofen
`binom_succ` writes the first throw out, `coin_bind_apply` splits it into `true` and `false`. Under the `do` the counts `true.toNat = 1` and `false.toNat = 0` (`Bool.toNat_true`, `Bool.toNat_false`), and `0 + Y` is `Y`: that needs `simp only` (it rewrites under `fun`). Then `bind_pure`, and the `true` branch is `shift_zero`.

*Tip.* `rw [binom_succ, coin_bind_apply]`, `simp only [Bool.toNat_true, Bool.toNat_false, zero_add, bind_pure]`, `rw [shift_zero, mul_zero, zero_add]`.
:::

:::proofde
`binom_succ` schreibt den ersten Wurf aus, `coin_bind_apply` teilt ihn in `true` und `false`. Unter dem `do` die Zahlen `true.toNat = 1` und `false.toNat = 0` (`Bool.toNat_true`, `Bool.toNat_false`), und `0 + Y` ist `Y`: Das braucht `simp only` (es schreibt unter `fun` um). Dann `bind_pure`, und der `true`-Zweig ist `shift_zero`.

*Tipp.* `rw [binom_succ, coin_bind_apply]`, `simp only [Bool.toNat_true, Bool.toNat_false, zero_add, bind_pure]`, `rw [shift_zero, mul_zero, zero_add]`.
:::
:::solution
```
rw [binom_succ, coin_bind_apply]
simp only [Bool.toNat_true, Bool.toNat_false, zero_add, bind_pure]
rw [shift_zero, mul_zero, zero_add]
```
:::
::::

::::leanonly (proof := "(p : I) (n k : ℕ) : binom p (n + 1) (k + 1) = ↑p * binom p n k + ↑(σ p) * binom p n (k + 1)") (lemma := "binom_succ_succ") (group := "chance.count") (uses := "binom_succ, coin_bind_apply, Bool.toNat_true, Bool.toNat_false, zero_add, bind_pure, shift_succ, binom_zero, add_zero, mul_zero, pure_bind, shift_zero")
:::en
*Pascal for masses.* $`k + 1` times `true` in $`n + 1` throws: the first is `true` and $`k` of the others are, or the first is `false` and $`k + 1` of the others are. Pascal's triangle, with masses.
:::

:::de
*Pascal für Massen.* $`k + 1`-mal `true` in $`n + 1` Würfen: Der erste ist `true` und $`k` der anderen sind es, oder der erste ist `false` und $`k + 1` der anderen sind es. Das Pascalsche Dreieck, mit Massen.
:::

:::proofen
As in the level before; at the end `shift_succ`.

*Tip.* `rw [binom_succ, coin_bind_apply]`, `simp only [Bool.toNat_true, Bool.toNat_false, zero_add, bind_pure]`, `rw [shift_succ]`.
:::

:::proofde
Wie im Level davor; am Ende `shift_succ`.

*Tipp.* `rw [binom_succ, coin_bind_apply]`, `simp only [Bool.toNat_true, Bool.toNat_false, zero_add, bind_pure]`, `rw [shift_succ]`.
:::
:::solution
```
rw [binom_succ, coin_bind_apply]
simp only [Bool.toNat_true, Bool.toNat_false, zero_add, bind_pure]
rw [shift_succ]
```
:::
::::

::::circuit (height := "600") (route := "count") (inputs := "x y z") (gates := "and, or, not") (coins := "p p p") (target := "bool true:(1-p)^3 false:1-(1-p)^3") (context := "Lean/Rules.lean") (proof := "(p : I) (n : ℕ) : binom p n 0 = ↑(σ p) ^ n") (lemma := "binom_all_false") (new := "pow_zero, pow_succ, mul_comm") (play := "a=or; b=or; c=not; x>a.0; y>a.1; a>b.0; z>b.1; b>c.0; c>out") (uses := "binom_zero, pure_self, pow_zero, binom_succ_zero, pow_succ, mul_comm, binom_succ, pure_zero_succ, binom_succ_succ")
:::en
*All false.* $`n` throws, all `false`: mass $`(1 - p)^n`.

On the board, three throws: build `true` exactly when all three are `false`.
:::

:::de
*Alle false.* $`n` Würfe, alle `false`: Masse $`(1 - p)^n`.

Auf dem Spielfeld drei Würfe: Bau `true` genau dann, wenn alle drei `false` sind.
:::

:::proofen
Induction on $`n` (from *Counting*): `pow_zero : a ^ 0 = 1`, `pow_succ : a ^ (n + 1) = a ^ n * a`.

*Tip.* `induction' n with n ih`; `rw [binom_zero, pure_self, pow_zero]`; `rw [binom_succ_zero, ih, pow_succ, mul_comm]`.
:::

:::proofde
Induktion über $`n` (aus *Zählen*): `pow_zero : a ^ 0 = 1`, `pow_succ : a ^ (n + 1) = a ^ n * a`.

*Tipp.* `induction' n with n ih`; `rw [binom_zero, pure_self, pow_zero]`; `rw [binom_succ_zero, ih, pow_succ, mul_comm]`.
:::
:::solution
```
induction' n with n ih
rw [binom_zero, pure_self, pow_zero]
rw [binom_succ_zero, ih, pow_succ, mul_comm]
```
:::
::::

::::leanonly (proof := "(p : I) (n k : ℕ) : binom p n (n + k + 1) = 0") (lemma := "binom_above") (new := "add_right_comm") (group := "chance.count") (uses := "zero_add, binom_zero, pure_zero_succ, binom_succ_succ, add_right_comm, add_assoc, mul_zero, add_zero, binom_succ, pure_self, binom_succ_zero, add_comm")
:::en
*Never more true than throws.* In $`n` throws there are at most $`n` times `true`.
:::

:::de
*Nie mehr true als Würfe.* In $`n` Würfen gibt es höchstens $`n`-mal `true`.
:::

:::proofen
Induction on $`n`, but the step needs the statement for another $`k` (once for $`k`, once for $`k + 1`). `induction' n with n ih generalizing k` makes `ih` hold for *every* $`k`. To use it, the numbers have to look as in `ih`: `add_right_comm : a + b + c = a + c + b` and `add_assoc`.

*Tip.* `induction' n with n ih generalizing k`; `rw [zero_add, binom_zero, pure_zero_succ]`; `rw [binom_succ_succ, add_right_comm n 1 k, ih, add_assoc n k 1, ih, mul_zero, mul_zero, add_zero]`.
:::

:::proofde
Induktion über $`n`, aber der Schritt braucht die Aussage für ein anderes $`k` (einmal für $`k`, einmal für $`k + 1`). `induction' n with n ih generalizing k` lässt `ih` für *jedes* $`k` gelten. Um es zu benutzen, müssen die Zahlen aussehen wie in `ih`: `add_right_comm : a + b + c = a + c + b` und `add_assoc`.

*Tipp.* `induction' n with n ih generalizing k`; `rw [zero_add, binom_zero, pure_zero_succ]`; `rw [binom_succ_succ, add_right_comm n 1 k, ih, add_assoc n k 1, ih, mul_zero, mul_zero, add_zero]`.
:::
:::solution
```
induction' n with n ih generalizing k
rw [zero_add, binom_zero, pure_zero_succ]
rw [binom_succ_succ, add_right_comm n 1 k, ih, add_assoc n k 1, ih, mul_zero, mul_zero, add_zero]
```
:::
::::

::::leanonly (proof := "(p : I) (n : ℕ) : binom p n n = ↑p ^ n") (lemma := "binom_diag") (group := "chance.count") (uses := "binom_zero, pure_self, pow_zero, binom_succ_succ, binom_above, mul_zero, add_zero, pow_succ, mul_comm, binom_succ, pure_zero_succ, binom_succ_zero, zero_add")
:::en
*All true.* $`n` throws, all `true`: mass $`p^n`.
:::

:::de
*Alle true.* $`n` Würfe, alle `true`: Masse $`p^n`.
:::

:::proofen
In the step, the second summand asks for $`n + 1` times `true` in $`n` throws: `binom_above p n 0` (Lean reads `n + 0 + 1` as `n + 1`).

*Tip.* `induction' n with n ih`; `rw [binom_zero, pure_self, pow_zero]`; `rw [binom_succ_succ, ih, binom_above p n 0, mul_zero, add_zero, pow_succ, mul_comm]`.
:::

:::proofde
Im Schritt fragt der zweite Summand nach $`n + 1`-mal `true` in $`n` Würfen: `binom_above p n 0` (Lean liest `n + 0 + 1` als `n + 1`).

*Tipp.* `induction' n with n ih`; `rw [binom_zero, pure_self, pow_zero]`; `rw [binom_succ_succ, ih, binom_above p n 0, mul_zero, add_zero, pow_succ, mul_comm]`.
:::
:::solution
```
induction' n with n ih
rw [binom_zero, pure_self, pow_zero]
rw [binom_succ_succ, ih, binom_above p n 0, mul_zero, add_zero, pow_succ, mul_comm]
```
:::
::::

::::leanonly (proof := "(p : I) (k m : ℕ) : binom p (k + m) k = ↑p ^ k * ↑(σ p) ^ m * ((k + m).choose k : ℝ≥0∞)") (lemma := "binom_formula") (new := "ring, one_mul, Nat.choose_self, Nat.choose_zero_right, Nat.choose_succ_succ', Nat.cast_add, Nat.cast_one") (group := "chance.count") (uses := "add_zero, binom_diag, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, zero_add, binom_all_false, one_mul, Nat.choose_zero_right, add_assoc, binom_succ_succ, add_right_comm, Nat.choose_succ_succ', Nat.cast_add, pow_succ, mul_zero, add_comm, binom_succ_zero")
:::en
*Boss: the binomial formula.* $`k` times `true` and $`m` times `false` in $`k + m` throws has the mass $`p^k (1 - p)^m \binom{k + m}{k}`. (Written with $`k + m` throws, there is no $`n - k`.)
:::

:::de
*Endgegner: die Binomialformel.* $`k`-mal `true` und $`m`-mal `false` in $`k + m` Würfen hat die Masse $`p^k (1 - p)^m \binom{k + m}{k}`. (Mit $`k + m` Würfen geschrieben, gibt es kein $`n - k`.)
:::

:::proofen
A double induction. On $`m`, for every $`k` (`generalizing k`): with $`m = 0` it is `binom_diag`. In the step on $`m`, an induction on $`k`: with $`k = 0` it is `binom_all_false`; else `binom_succ_succ` splits the first throw, the first summand is `ih2` (one `true` less), the second `ih (k + 1)` (one `false` less). Bring the numbers into their form with `add_right_comm` and `add_assoc`. Pascal's triangle `Nat.choose_succ_succ' : (n + 1).choose (k + 1) = n.choose k + n.choose (k + 1)`, `Nat.cast_add` takes the sum out of `↑`, and what is left is computing: `ring`.

*Tip.* `induction' m with m ih generalizing k`; `rw [add_zero, binom_diag, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, mul_one]`; `induction' k with k ih2`; `rw [zero_add, binom_all_false, pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one]`; `rw [← add_assoc, binom_succ_succ, ih (k + 1), add_right_comm k 1 m, add_assoc k m 1, ih2]`, `rw [Nat.choose_succ_succ', Nat.cast_add]`, `ring`.
:::

:::proofde
Eine doppelte Induktion. Über $`m`, für jedes $`k` (`generalizing k`): Mit $`m = 0` ist es `binom_diag`. Im Schritt über $`m` eine Induktion über $`k`: Mit $`k = 0` ist es `binom_all_false`; sonst teilt `binom_succ_succ` den ersten Wurf, der erste Summand ist `ih2` (ein `true` weniger), der zweite `ih (k + 1)` (ein `false` weniger). Bring die Zahlen mit `add_right_comm` und `add_assoc` in ihre Form. Das Pascalsche Dreieck `Nat.choose_succ_succ' : (n + 1).choose (k + 1) = n.choose k + n.choose (k + 1)`, `Nat.cast_add` holt die Summe aus `↑`, und was bleibt, ist Rechnen: `ring`.

*Tipp.* `induction' m with m ih generalizing k`; `rw [add_zero, binom_diag, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, mul_one]`; `induction' k with k ih2`; `rw [zero_add, binom_all_false, pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one]`; `rw [← add_assoc, binom_succ_succ, ih (k + 1), add_right_comm k 1 m, add_assoc k m 1, ih2]`, `rw [Nat.choose_succ_succ', Nat.cast_add]`, `ring`.
:::
:::solution
```
induction' m with m ih generalizing k
rw [add_zero, binom_diag, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, mul_one]
induction' k with k ih2
rw [zero_add, binom_all_false, pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one]
rw [← add_assoc, binom_succ_succ, ih (k + 1), add_right_comm k 1 m, add_assoc k m 1, ih2]
rw [Nat.choose_succ_succ', Nat.cast_add]
ring
```
:::
::::

::::circuit (height := "700") (size := "big") (route := "count") (inputs := "x y z") (gates := "not, toNat, plus") (coins := "p p p") (target := "nat 0:p^3 1:3p^2(1-p) 2:3p(1-p)^2 3:(1-p)^3") (context := "Lean/Rules.lean") (proof := "(p : I) (k m : ℕ) : binom (σ p) (k + m) m = binom p (k + m) k") (lemma := "binom_symm") (new := "symm_twice, Nat.choose_symm_add") (play := "a=not; b=not; c=not; d=toNat; e=toNat; f=toNat; g=plus; h=plus; x>a.0; y>b.0; z>c.0; a>d.0; b>e.0; c>f.0; d>g.0; e>g.1; g>h.0; f>h.1; h>out") (uses := "add_comm, binom_formula, symm_twice, Nat.choose_symm_add, add_assoc")
:::en
*Encore: true and false swapped.* $`m` times `true` with the coin $`1 - p` is as likely as $`k` times `true` with the coin $`p`: count the `false` instead of the `true`. With your formula, this is computing.

On the board, three throws of the coin `p`: count the `false`. The target is binomial with $`1 - p`.
:::

:::de
*Zugabe: true und false getauscht.* $`m`-mal `true` mit der Münze $`1 - p` ist so wahrscheinlich wie $`k`-mal `true` mit der Münze $`p`: Zähl die `false` statt der `true`. Mit deiner Formel ist das Rechnen.

Auf dem Spielfeld drei Würfe der Münze `p`: Zähl die `false`. Das Ziel ist binomial mit $`1 - p`.
:::

:::proofen
Bring both sides into the form of `binom_formula` (`add_comm`), use it twice; `symm_twice : σ (σ p) = p` and `Nat.choose_symm_add : (m + k).choose m = (m + k).choose k`; then `ring`.

*Tip.* `rw [add_comm k m, binom_formula, add_comm m k, binom_formula, symm_twice, Nat.choose_symm_add]`, `ring`.
:::

:::proofde
Bring beide Seiten in die Form von `binom_formula` (`add_comm`), benutze sie zweimal; `symm_twice : σ (σ p) = p` und `Nat.choose_symm_add : (m + k).choose m = (m + k).choose k`; dann `ring`.

*Tipp.* `rw [add_comm k m, binom_formula, add_comm m k, binom_formula, symm_twice, Nat.choose_symm_add]`, `ring`.
:::
:::solution
```
rw [add_comm k m, binom_formula, add_comm m k, binom_formula, symm_twice, Nat.choose_symm_add]
ring
```
:::
::::
