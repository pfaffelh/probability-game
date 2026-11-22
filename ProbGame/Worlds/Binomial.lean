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
`Bool`, then the masses of the coin. What you prove is unlocked as `coin_bind_apply`, with the mark
*simp*: from now on `simp` uses it by itself.
:::

:::proofde
Wie bei `bind_true`: `bind_apply : (do let a ← μ; f a) b = ∑ a, μ a * f a b` und die zwei Summanden einer
Summe über `Bool`, dann die Massen der Münze. Was du beweist, wird als `coin_bind_apply`
freigeschaltet, mit der Marke *simp*: Ab jetzt benutzt `simp` es von selbst.
:::
:::solution
```
rw [bind_apply, Fintype.sum_bool, coin_true, coin_false]
```
:::
::::

::::leanonly (proof := "{α : Type} [DecidableEq α] (a : α) : (pure a : DiscreteMeasure α) a = 1") (lemma := "pure_self") (group := "chance.count") (uses := "pure_apply, beq_self_eq_true, Bool.cond_true, Bool.cond_false")
:::en
*At its point.* A point mass has mass one at its point, now on any type.
:::

:::de
*An ihrem Punkt.* Eine Punktmasse hat an ihrem Punkt die Masse eins, jetzt auf jedem Typ.
:::

:::proofen
`pure_apply : (pure a) b = bif a == b then 1 else 0`, from *One Coin*; and
`beq_self_eq_true : (a == a) = true`. What you prove is unlocked as `pure_self`, with the mark *simp*.
:::

:::proofde
`pure_apply : (pure a) b = bif a == b then 1 else 0`, aus *Eine Münze*; und
`beq_self_eq_true : (a == a) = true`. Was du beweist, wird als `pure_self` freigeschaltet, mit der
Marke *simp*.
:::
:::solution
```
rw [pure_apply, beq_self_eq_true, Bool.cond_true]
```
:::
::::

:::::leanonly (proof := "(p : I) (k : ℕ) : binom p 0 0 = ⟦1 ‖ 1, 0, ↑p⟧ ∧ binom p 0 (k + 1) = ⟦0 ‖ 0, 1, ↑p⟧") (new := "pure_zero_succ") (group := "chance.count") (uses := "binom_zero, pure_self, pure_zero_succ, binom_succ")
::::hint (anchor := "gap")
:::en
With no throw: how often `true`?
:::

:::de
Ohne Wurf: wie oft `true`?
:::
::::

:::en
*No throw.* `binom p 0 = pure 0` (in *Counting*): what does it say about the masses?
:::

:::de
*Kein Wurf.* `binom p 0 = pure 0` (in *Zählen*): Was sagt das über die Massen?
:::

:::proofen
Two statements joined by `∧`: `constructor`, as in *Masses*. For the second,
`pure_zero_succ : (pure 0) (k + 1) = 0`.
:::

:::proofde
Zwei Aussagen, verbunden mit `∧`: `constructor`, wie in *Massen*. Für das zweite
`pure_zero_succ : (pure 0) (k + 1) = 0`.
:::
:::solution
```
constructor
rw [binom_zero, pure_self]
rw [binom_zero, pure_zero_succ]
```
:::
:::::

::::leanonly (proof := "(μ : DiscreteMeasure ℕ) (k : ℕ) : (do let Y ← μ; pure (1 + Y)) (k + 1) + (do let Y ← μ; pure (1 + Y)) 0 = μ k") (new := "shift_succ, shift_zero") (group := "chance.count") (uses := "shift_succ, shift_zero, add_zero, zero_add")
:::en
*One more.* Adding one to every outcome shifts the bars one place to the right: the mass at `k + 1` is the old mass at `k`, and at `0` there is nothing.
:::

:::de
*Eins mehr.* Eins zu jedem Ergebnis addieren schiebt die Säulen eine Stelle nach rechts: Die Masse bei `k + 1` ist die alte Masse bei `k`, und bei `0` ist nichts.
:::

:::proofen
`shift_succ : (do let Y ← μ; pure (1 + Y)) (k + 1) = μ k` and `shift_zero : (do let Y ← μ; pure (1 + Y)) 0 = 0`. After this level both carry the mark *simp*.
:::

:::proofde
`shift_succ : (do let Y ← μ; pure (1 + Y)) (k + 1) = μ k` und `shift_zero : (do let Y ← μ; pure (1 + Y)) 0 = 0`. Nach diesem Level tragen beide die Marke *simp*.
:::
:::solution
```
rw [shift_succ, shift_zero, add_zero]
```
:::
::::

::::leanonly (proof := "(p : I) (n : ℕ) : binom p (n + 1) 0 = ↑(σ p) * binom p n 0") (lemma := "binom_succ_zero") (new := "mul_zero") (group := "chance.count") (uses := "binom_succ, mul_zero, binom_zero, zero_add")
:::en
*No true in one throw more.* No `true` in $`n + 1` throws: the first is `false`, and none in the other $`n`.
:::

:::de
*Kein true in einem Wurf mehr.* Kein `true` in $`n + 1` Würfen: Der erste ist `false`, und in den anderen $`n` keins.
:::

:::proofen
`binom_succ` writes the first throw out. The rest is computing, and the rules for it carry the mark
*simp*: `coin_bind_apply` splits the throw into `true` and `false`, `Bool.toNat_true` and `Bool.toNat_false` count it, the
`true` branch is `shift_zero`, and `bind_pure` cleans up. One rule is new: `mul_zero : a * 0 = 0`.
`simp` does not use a rule by itself in the level that brings it; you give it to `simp` with `simp [h]`.
:::

:::proofde
`binom_succ` schreibt den ersten Wurf aus. Der Rest ist Rechnen, und die Regeln dafür tragen die
Marke *simp*: `coin_bind_apply` teilt den Wurf in `true` und `false`, `Bool.toNat_true` und `Bool.toNat_false` zählen ihn, der
`true`-Zweig ist `shift_zero`, und `bind_pure` räumt auf. Eine Regel ist neu: `mul_zero : a * 0 = 0`.
In dem Level, das eine Regel bringt, benutzt `simp` sie nicht von selbst; du gibst sie ihm mit `simp [h]`.
:::
:::solution
```
rw [binom_succ]
simp [mul_zero]
```
:::
::::

::::leanonly (proof := "(p : I) (n k : ℕ) : binom p (n + 1) (k + 1) = ↑p * binom p n k + ↑(σ p) * binom p n (k + 1)") (lemma := "binom_succ_succ") (group := "chance.count") (uses := "binom_succ, binom_zero")
:::en
*Pascal for masses.* $`k + 1` times `true` in $`n + 1` throws: the first is `true` and $`k` of the others are, or the first is `false` and $`k + 1` of the others are. Pascal's triangle, with masses.
:::

:::de
*Pascal für Massen.* $`k + 1`-mal `true` in $`n + 1` Würfen: Der erste ist `true` und $`k` der anderen sind es, oder der erste ist `false` und $`k + 1` der anderen sind es. Das Pascalsche Dreieck, mit Massen.
:::

:::proofen
As in the level before, now with `shift_succ`, which `simp` also knows. What you prove is unlocked as
`binom_succ_succ`.
:::

:::proofde
Wie im Level davor, jetzt mit `shift_succ`, das `simp` auch kennt. Was du beweist, wird als
`binom_succ_succ` freigeschaltet.
:::
:::solution
```
rw [binom_succ]
simp
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
:::

:::proofde
Induktion über $`n` (aus *Zählen*): `pow_zero : a ^ 0 = 1`, `pow_succ : a ^ (n + 1) = a ^ n * a`.
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
:::

:::proofde
Im Schritt fragt der zweite Summand nach $`n + 1`-mal `true` in $`n` Würfen: `binom_above p n 0` (Lean liest `n + 0 + 1` als `n + 1`).
:::
:::solution
```
induction' n with n ih
rw [binom_zero, pure_self, pow_zero]
rw [binom_succ_succ, ih, binom_above p n 0, mul_zero, add_zero, pow_succ, mul_comm]
```
:::
::::

::::leanonly (proof := "(n : ℕ) : (n.choose 0 : ℝ≥0∞) = 1 ∧ 1 * (n.choose n : ℝ≥0∞) = 1") (new := "Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, one_mul") (group := "chance.count") (uses := "Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.choose_self, Nat.cast_add, mul_one")
:::en
*The edges of Pascal's triangle.* `n.choose k` is the number of ways to choose $`k` out of $`n`: $`\binom{n}{k}`. None of $`n`, or all of $`n`: one way each.
:::

:::de
*Die Ränder des Pascalschen Dreiecks.* `n.choose k` ist die Anzahl der Möglichkeiten, $`k` aus $`n` zu wählen: $`\binom{n}{k}`. Keins aus $`n`, oder alle aus $`n`: je eine Möglichkeit.
:::

:::proofen
`Nat.choose_zero_right : n.choose 0 = 1` and `Nat.choose_self : n.choose n = 1` are about natural numbers; in the statement they stand as masses, `(↑(n.choose 0) : ℝ≥0∞)`. `Nat.cast_one : ↑1 = 1` makes the natural number `1` the mass `1`. And `one_mul : 1 * a = a`. Two statements again: `constructor`.
:::

:::proofde
`Nat.choose_zero_right : n.choose 0 = 1` und `Nat.choose_self : n.choose n = 1` handeln von natürlichen Zahlen; in der Aussage stehen sie als Massen, `(↑(n.choose 0) : ℝ≥0∞)`. `Nat.cast_one : ↑1 = 1` macht aus der natürlichen Zahl `1` die Masse `1`. Und `one_mul : 1 * a = a`. Wieder zwei Aussagen: `constructor`.
:::
:::solution
```
constructor
rw [Nat.choose_zero_right, Nat.cast_one]
rw [one_mul, Nat.choose_self, Nat.cast_one]
```
:::
::::

:::::leanonly (proof := "(n k : ℕ) : ((n + 1).choose (k + 1) : ℝ≥0∞) = (n.choose ⟦k ‖ k, k + 1, k + 2⟧ : ℝ≥0∞) + (n.choose (k + 1) : ℝ≥0∞)") (new := "Nat.choose_succ_succ', Nat.cast_add") (group := "chance.count") (uses := "Nat.choose_succ_succ', Nat.cast_add, Nat.cast_one")
::::hint (anchor := "gap")
:::en
One of the $`n + 1` is the first. It is chosen, or it is not: how many are then still to choose among the other $`n`?
:::

:::de
Eines der $`n + 1` ist das erste. Es wird gewählt oder nicht: Wie viele sind dann noch unter den anderen $`n` zu wählen?
:::
::::

:::en
*Pascal's triangle.* $`k + 1` out of $`n + 1`: with the first, or without it.
:::

:::de
*Das Pascalsche Dreieck.* $`k + 1` aus $`n + 1`: mit dem ersten, oder ohne es.
:::

:::proofen
`Nat.choose_succ_succ' : (n + 1).choose (k + 1) = n.choose k + n.choose (k + 1)`, for natural numbers. Then the sum stands inside `↑`: `Nat.cast_add : ↑(a + b) = ↑a + ↑b` takes it out.
:::

:::proofde
`Nat.choose_succ_succ' : (n + 1).choose (k + 1) = n.choose k + n.choose (k + 1)`, für natürliche Zahlen. Dann steht die Summe in `↑`: `Nat.cast_add : ↑(a + b) = ↑a + ↑b` holt sie heraus.
:::
:::solution
```
rw [Nat.choose_succ_succ', Nat.cast_add]
```
:::
:::::

::::leanonly (proof := "(a b x y : ℝ≥0∞) (k m : ℕ) : a * (a ^ k * b ^ (m + 1) * x) + b * (a ^ (k + 1) * b ^ m * y) = a ^ (k + 1) * b ^ (m + 1) * (x + y)") (group := "chance.count") (uses := "-")
:::en
*Computing with powers.* Both summands have the same powers of `a` and `b`. Seen at once, tedious rule by rule.
:::

:::de
*Rechnen mit Potenzen.* Beide Summanden haben dieselben Potenzen von `a` und `b`. Auf einen Blick zu sehen, Regel für Regel mühsam.
:::

:::proofen
An equation that holds by computing with `+`, `*` and powers alone: the tactic for that is from *Two Coins*.
:::

:::proofde
Eine Gleichung, die allein durch Rechnen mit `+`, `*` und Potenzen gilt: Die Taktik dafür ist aus *Zwei Münzen*.
:::
:::solution
```
ring
```
:::
::::

::::leanonly (proof := "(p : I) (k m : ℕ) : binom p (k + m) k = ↑p ^ k * ↑(σ p) ^ m * ((k + m).choose k : ℝ≥0∞)") (lemma := "binom_formula") (group := "chance.count") (uses := "add_zero, binom_diag, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, zero_add, binom_all_false, one_mul, Nat.choose_zero_right, add_assoc, binom_succ_succ, add_right_comm, Nat.choose_succ_succ', Nat.cast_add, pow_succ, mul_zero, add_comm, binom_succ_zero")
:::en
*Boss: the binomial formula.* $`k` times `true` and $`m` times `false` in $`k + m` throws has the mass $`p^k (1 - p)^m \binom{k + m}{k}`. (Written with $`k + m` throws, there is no $`n - k`.)
:::

:::de
*Endgegner: die Binomialformel.* $`k`-mal `true` und $`m`-mal `false` in $`k + m` Würfen hat die Masse $`p^k (1 - p)^m \binom{k + m}{k}`. (Mit $`k + m` Würfen geschrieben, gibt es kein $`n - k`.)
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
:::

:::proofde
Bring beide Seiten in die Form von `binom_formula` (`add_comm`), benutze sie zweimal; `symm_twice : σ (σ p) = p` und `Nat.choose_symm_add : (m + k).choose m = (m + k).choose k`; dann `ring`.
:::
:::solution
```
rw [add_comm k m, binom_formula, add_comm m k, binom_formula, symm_twice, Nat.choose_symm_add]
ring
```
:::
::::
