import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Binomial" =>

%%%
htmlSplit := .never
%%%

:::en
`binom p n` is the number of `true` in $`n` throws of a coin `p`, defined by recursion on $`n` (in *Counting*). Here its masses: by induction, Pascal's triangle with masses, up to the binomial formula. And thinning comes back: a thinned binomial is binomial. In Lean only.
:::

:::de
`binom p n` ist die Anzahl der `true` in $`n` Würfen einer Münze `p`, durch Rekursion über $`n` definiert (in *Zählen*). Hier ihre Massen: durch Induktion, das Pascalsche Dreieck mit Massen, bis zur Binomialformel. Und das Ausdünnen kommt zurück: Eine ausgedünnte Binomialverteilung ist binomial. Nur in Lean.
:::

::::leanonly (proof := "(p : I) (μ ν : DiscreteMeasure ℕ) (k : ℕ) : (do let x ← coin p; bif x then μ else ν) k = ↑p * μ k + ↑(σ p) * ν k") (new := "coin_bind_apply") (group := "chance.count") (uses := "coin_bind_apply, Bool.cond_true, Bool.cond_false")
:::en
*A coin first.* A draw that starts with a coin `p`: the mass at `k` comes through `true` (mass $`p`) and through `false` (mass $`1 - p`). That is `bind_true` again, now at any point `k`.
:::

:::de
*Erst eine Münze.* Ein Ziehen, das mit einer Münze `p` beginnt: Die Masse bei `k` kommt über `true` (Masse $`p`) und über `false` (Masse $`1 - p`). Das ist wieder `bind_true`, jetzt an jedem Punkt `k`.
:::

:::proofen
`coin_bind_apply : (coin p >>= f) x = ↑p * f true x + ↑(σ p) * f false x`.

*Tip.* `rw [coin_bind_apply, Bool.cond_true, Bool.cond_false]`.
:::

:::proofde
`coin_bind_apply : (coin p >>= f) x = ↑p * f true x + ↑(σ p) * f false x`.

*Tipp.* `rw [coin_bind_apply, Bool.cond_true, Bool.cond_false]`.
:::
:::solution
```
rw [coin_bind_apply, Bool.cond_true, Bool.cond_false]
```
:::
::::

::::leanonly (proof := "(p : I) : binom p 0 0 = 1") (new := "pure_self") (group := "chance.count") (uses := "binom_zero, pure_self, binom_succ, pure_zero_succ")
:::en
*No throw.* With no throw, surely no `true`.
:::

:::de
*Kein Wurf.* Ohne Wurf sicher kein `true`.
:::

:::proofen
`pure_self : (pure a) a = 1`.

*Tip.* `rw [binom_zero, pure_self]`.
:::

:::proofde
`pure_self : (pure a) a = 1`.

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

::::leanonly (proof := "(p : I) (n : ℕ) : binom p (n + 1) 0 = ↑(σ p) * binom p n 0") (lemma := "binom_succ_zero") (new := "Bool.toNat_false") (group := "chance.count") (uses := "binom_succ, coin_bind_apply, Bool.toNat_true, Bool.toNat_false, zero_add, bind_pure, shift_zero, mul_zero, binom_zero, add_zero, pure_bind, shift_succ")
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

::::leanonly (proof := "(p : I) (n : ℕ) : binom p n 0 = ↑(σ p) ^ n") (lemma := "binom_all_false") (new := "pow_zero, pow_succ") (group := "chance.count") (uses := "binom_zero, pure_self, pow_zero, binom_succ_zero, pow_succ, mul_comm, binom_succ, pure_zero_succ, binom_succ_succ")
:::en
*All false.* $`n` throws, all `false`: mass $`(1 - p)^n`.
:::

:::de
*Alle false.* $`n` Würfe, alle `false`: Masse $`(1 - p)^n`.
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

::::leanonly (proof := "(p q : I) : (do let C ← coin p; binom q C.toNat) = (do let B ← coin (p * q); pure B.toNat)") (lemma := "coin_bind_binom") (group := "chance.count") (uses := "coin_thin, bind_assoc, Bool.toNat_false, binom_zero, Bool.cond_false, pure_bind, Bool.toNat_true, Bool.cond_true, binom_succ, add_zero, bind_pure, zero_add")
:::en
*Thinning comes back.* A coin `p`, and then as many coins `q` as it shows (one or none), counted: that is your thinned coin from *Thinning*, counted.
:::

:::de
*Das Ausdünnen kommt zurück.* Eine Münze `p`, und dann so viele Münzen `q`, wie sie zeigt (eine oder keine), gezählt: Das ist deine ausgedünnte Münze aus *Ausdünnen*, gezählt.
:::

:::proofen
`rw [← coin_thin]` writes the coin `p * q` as the thinned coin. Then both sides start with `coin p`: `congr 1`, `funext x`, `cases x`.

*Tip.* `rw [← coin_thin]`, `simp only [bind_assoc]`, `congr 1`, `funext x`, `cases x`; at `false`: `rw [Bool.toNat_false, binom_zero, Bool.cond_false, pure_bind, Bool.toNat_false]`; at `true`: `rw [Bool.toNat_true, Bool.cond_true, binom_succ, binom_zero]`, `simp only [pure_bind, add_zero]`.
:::

:::proofde
`rw [← coin_thin]` schreibt die Münze `p * q` als ausgedünnte Münze. Dann beginnen beide Seiten mit `coin p`: `congr 1`, `funext x`, `cases x`.

*Tipp.* `rw [← coin_thin]`, `simp only [bind_assoc]`, `congr 1`, `funext x`, `cases x`; bei `false`: `rw [Bool.toNat_false, binom_zero, Bool.cond_false, pure_bind, Bool.toNat_false]`; bei `true`: `rw [Bool.toNat_true, Bool.cond_true, binom_succ, binom_zero]`, `simp only [pure_bind, add_zero]`.
:::
:::solution
```
rw [← coin_thin]
simp only [bind_assoc]
congr 1
funext x
cases x
rw [Bool.toNat_false, binom_zero, Bool.cond_false, pure_bind, Bool.toNat_false]
rw [Bool.toNat_true, Bool.cond_true, binom_succ, binom_zero]
simp only [pure_bind, add_zero]
```
:::
::::

::::leanonly (proof := "(p q : I) (f : ℕ → DiscreteMeasure ℕ) : (do let C ← coin p; let U ← binom q C.toNat; f U) = (do let B ← coin (p * q); f B.toNat)") (lemma := "coin_bind_binom'") (group := "chance.count") (uses := "bind_assoc, coin_bind_binom, pure_bind, bind_pure")
:::en
*With something after it.* The same, when the `do` block goes on.
:::

:::de
*Mit etwas danach.* Dasselbe, wenn der `do`-Block weitergeht.
:::

:::proofen
Make the first two steps a block of their own, use your lemma, and split again.

*Tip.* `rw [← bind_assoc, coin_bind_binom, bind_assoc]`, `simp only [pure_bind]`.
:::

:::proofde
Mach die ersten zwei Schritte zu einem eigenen Block, benutze dein Lemma, und teile wieder.

*Tipp.* `rw [← bind_assoc, coin_bind_binom, bind_assoc]`, `simp only [pure_bind]`.
:::
:::solution
```
rw [← bind_assoc, coin_bind_binom, bind_assoc]
simp only [pure_bind]
```
:::
::::

::::leanonly (proof := "(p q : I) (n : ℕ) : (do let X ← binom p n; binom q X) = binom (p * q) n") (lemma := "binom_thin") (new := "bind_comm") (group := "chance.count") (uses := "binom_zero, pure_bind, binom_succ, bind_assoc, binom_add, bind_comm, coin_bind_binom', bind_pure")
:::en
*Thinning a binomial.* Of $`n` throws with $`p`, each `true` is kept with probability $`q`. The number kept is binomial with $`p q`.
:::

:::de
*Eine Binomialverteilung ausdünnen.* Von $`n` Würfen mit $`p` wird jedes `true` mit Wahrscheinlichkeit $`q` behalten. Die Anzahl der behaltenen ist binomial mit $`p q`.
:::

:::proofen
Induction on $`n`. In the step, the first coin `C` and the other throws `X`: of `C.toNat + X`, keep is `binom q (C.toNat + X)`, by `binom_add` read backwards the sum of two independent parts. `bind_comm` swaps two independent draws, so that the part of the first coin comes first; then your last lemma.

*Tip.* `induction' n with n ih`; `rw [binom_zero, binom_zero, pure_bind, binom_zero]`; `rw [binom_succ, binom_succ (p * q), ← ih]`, `simp only [bind_assoc, pure_bind]`, `simp only [← binom_add]`, `simp only [bind_comm (binom p n) (binom q _)]`, `rw [coin_bind_binom']`.
:::

:::proofde
Induktion über $`n`. Im Schritt die erste Münze `C` und die anderen Würfe `X`: Von `C.toNat + X` behalten ist `binom q (C.toNat + X)`, nach `binom_add` rückwärts die Summe zweier unabhängiger Teile. `bind_comm` tauscht zwei unabhängige Ziehungen, damit der Teil der ersten Münze vorne steht; dann dein letztes Lemma.

*Tipp.* `induction' n with n ih`; `rw [binom_zero, binom_zero, pure_bind, binom_zero]`; `rw [binom_succ, binom_succ (p * q), ← ih]`, `simp only [bind_assoc, pure_bind]`, `simp only [← binom_add]`, `simp only [bind_comm (binom p n) (binom q _)]`, `rw [coin_bind_binom']`.
:::
:::solution
```
induction' n with n ih
rw [binom_zero, binom_zero, pure_bind, binom_zero]
rw [binom_succ, binom_succ (p * q), ← ih]
simp only [bind_assoc, pure_bind]
simp only [← binom_add]
simp only [bind_comm (binom p n) (binom q _)]
rw [coin_bind_binom']
```
:::
::::

::::leanonly (proof := "(p : I) (k m : ℕ) : binom p (k + m) k = ↑p ^ k * ↑(σ p) ^ m * ((k + m).choose k : ENNReal)") (lemma := "binom_formula") (new := "ring, one_mul, Nat.choose_self, Nat.choose_zero_right, Nat.choose_succ_succ', Nat.cast_add, Nat.cast_one") (group := "chance.count") (uses := "add_zero, binom_diag, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, zero_add, binom_all_false, one_mul, Nat.choose_zero_right, add_assoc, binom_succ_succ, add_right_comm, Nat.choose_succ_succ', Nat.cast_add, pow_succ, mul_zero, add_comm, binom_succ_zero")
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

::::leanonly (proof := "(p : I) (k m : ℕ) : binom (σ p) (k + m) m = binom p (k + m) k") (lemma := "binom_symm") (new := "symm_twice, Nat.choose_symm_add") (group := "chance.count") (uses := "add_comm, binom_formula, symm_twice, Nat.choose_symm_add, add_assoc")
:::en
*Encore: true and false swapped.* $`m` times `true` with the coin $`1 - p` is as likely as $`k` times `true` with the coin $`p`: count the `false` instead of the `true`. With your formula, this is computing.
:::

:::de
*Zugabe: true und false getauscht.* $`m`-mal `true` mit der Münze $`1 - p` ist so wahrscheinlich wie $`k`-mal `true` mit der Münze $`p`: Zähl die `false` statt der `true`. Mit deiner Formel ist das Rechnen.
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
