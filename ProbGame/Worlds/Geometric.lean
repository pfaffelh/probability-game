import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Geometric" =>

%%%
htmlSplit := .never
%%%

:::en
How long until the first `true`? A coin that is thrown again while it shows `false`: the second stage of *Multi-Stage Experiments*, again and again. The geometric distribution: its masses step by step, its formula, its lack of memory, and the `do` block that waits. In Lean only.
:::

:::de
Wie lange bis zum ersten `true`? Eine Münze, die nochmal geworfen wird, solange sie `false` zeigt: die zweite Stufe aus *Mehrstufige Experimente*, immer wieder. Die geometrische Verteilung: ihre Massen Schritt für Schritt, ihre Formel, ihre Gedächtnislosigkeit, und der `do`-Block, der wartet. Nur in Lean.
:::

::::leanonly (proof := "(p : I) : (do let x ← coin p; bif x then pure false else coin p) true = (⟦↑(σ p) * ↑p ‖ ↑p * ↑p, ↑(σ p) * ↑p, ↑(σ p), ↑p⟧ : ℝ≥0∞)") (group := "chance.count") (uses := "bind_true, coin_bind_apply, Bool.cond_true, Bool.cond_false, pure_true, mul_zero, zero_add, coin_true, coin_false, add_zero, coin_total, rw, simp")
:::en
*At the second throw.* Throw a coin `p` until it shows `true`. This block says `true` exactly when that happens at the second throw: a `true` at once does not count, and after a `false` the second throw decides.
:::

:::de
*Beim zweiten Wurf.* Wirf eine Münze `p`, bis sie `true` zeigt. Dieser Block sagt `true` genau dann, wenn das beim zweiten Wurf passiert: Ein `true` sofort zählt nicht, und nach einem `false` entscheidet der zweite Wurf.
:::

:::proofen
A second stage, as in *Multi-Stage Experiments*.
:::

:::proofde
Eine zweite Stufe, wie in *Mehrstufige Experimente*.
:::
:::solution
```
rw [bind_true]
simp
```
:::
:::solution
```
simp
```
:::
:::solution
```
rw [coin_bind_apply]
simp
```
:::
:::solution
```
rw [bind_true, Bool.cond_true, Bool.cond_false, pure_true, Bool.cond_false, mul_zero, zero_add, coin_true, coin_false]
```
:::
::::

::::leanonly (proof := "(p : I) : (do let x ← coin p; bif x then pure false else (do let y ← coin p; bif y then pure false else coin p)) true = (⟦↑(σ p) * (↑(σ p) * ↑p) ‖ ↑(σ p) * ↑p, ↑p * (↑p * ↑(σ p)), ↑(σ p) * (↑(σ p) * ↑p), ↑(σ p) * ↑(σ p)⟧ : ℝ≥0∞)") (group := "chance.count") (uses := "bind_true, Bool.cond_true, Bool.cond_false, pure_true, mul_zero, zero_add, coin_true, coin_false, add_zero, coin_total, rw, simp")
:::en
*At the third throw.* `true` exactly when the first `true` comes at the third throw: an experiment in three stages.
:::

:::de
*Beim dritten Wurf.* `true` genau dann, wenn das erste `true` beim dritten Wurf kommt: ein Experiment in drei Stufen.
:::

:::proofen
The first throw as before; what follows is a `do` block again.
:::

:::proofde
Der erste Wurf wie eben; was folgt, ist wieder ein `do`-Block.
:::
:::solution
```
rw [bind_true]
simp [bind_true]
```
:::
:::solution
```
simp
```
:::
:::solution
```
rw [bind_true]
simp
```
:::
:::solution
```
rw [bind_true, Bool.cond_true, Bool.cond_false, pure_true, Bool.cond_false, mul_zero, zero_add]
rw [bind_true, Bool.cond_true, Bool.cond_false, pure_true, Bool.cond_false, mul_zero, zero_add]
rw [coin_true, coin_false]
```
:::
::::

::::leanonly (proof := "(p : I) : geom p 0 = ⟦↑p ‖ ↑(σ p), ↑p, 1, 0⟧") (lemma := "geom_zero") (group := "chance.count") (uses := "rfl")
:::en
*True at once.* Now with a number: `geom p` is the number of `false` before the first `true`. Its masses are defined step by step, as you just computed them. The first step: `true` at once, no `false` before.
:::

:::de
*Sofort true.* Jetzt mit einer Zahl: `geom p` ist die Anzahl der `false` vor dem ersten `true`. Ihre Massen sind Schritt für Schritt definiert, so wie du sie gerade ausgerechnet hast. Der erste Schritt: sofort `true`, kein `false` davor.
:::

:::proofen
The definition:

```
def geomMass (p : I) : ℕ → ℝ≥0∞
  | 0 => …
  | k + 1 => … * geomMass p k

def geom (p : I) : DiscreteMeasure ℕ := ⟨geomMass p⟩
```

(The two places left open are yours: in this level and the next.) The first case.
:::

:::proofde
Die Definition:

```
def geomMass (p : I) : ℕ → ℝ≥0∞
  | 0 => …
  | k + 1 => … * geomMass p k

def geom (p : I) : DiscreteMeasure ℕ := ⟨geomMass p⟩
```

(Die zwei offenen Stellen sind deine: in diesem Level und im nächsten.) Der erste Fall.
:::
:::solution
```
rfl
```
:::
::::

::::leanonly (proof := "(p : I) (k : ℕ) : geom p (k + 1) = ⟦↑(σ p) ‖ ↑p, ↑(σ p), ↑(σ p) ^ k, 1⟧ * geom p k") (lemma := "geom_succ") (group := "chance.count") (uses := "rfl")
:::en
*One false more.* One `false` more before the first `true`: the mass gets one factor more, as from the second throw to the third.
:::

:::de
*Ein false mehr.* Ein `false` mehr vor dem ersten `true`: Die Masse bekommt einen Faktor mehr, wie vom zweiten Wurf zum dritten.
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

::::leanonly (proof := "(p : I) : (do let x ← coin p; let y ← (bif x then pure true else coin p); let z ← (bif y then pure true else coin p); pure z) true = geom p 0 + geom p 1 + geom p 2") (group := "chance.count") (uses := "bind_true, geom_succ, geom_zero, mul_add, add_assoc, add_comm, add_right_comm, ring, rw, simp")
:::en
*Three tries.* The boss of *Multi-Stage Experiments*: throw until `true` comes, at most three times. It comes at the first throw, at the second, or at the third: three masses of `geom p`.
:::

:::de
*Drei Versuche.* Der Endgegner aus *Mehrstufige Experimente*: Wirf, bis `true` kommt, höchstens dreimal. Es kommt beim ersten Wurf, beim zweiten oder beim dritten: drei Massen von `geom p`.
:::

:::proofen
The left side as in the first levels of this world. On the right, the two cases of the definition
write the masses out.
:::

:::proofde
Die linke Seite wie in den ersten Leveln dieser Welt. Rechts schreiben die zwei Fälle der Definition
die Massen aus.
:::
:::solution
```
rw [bind_true]
simp [bind_true]
rw [geom_succ, geom_succ, geom_succ, geom_zero]
ring
```
:::
:::solution
```
simp
rw [geom_succ, geom_succ, geom_succ, geom_zero]
ring
```
:::
:::solution
```
rw [geom_succ, geom_succ, geom_succ, geom_zero]
simp
ring
```
:::
:::solution
```
rw [bind_true]
simp
rw [geom_succ, geom_succ, geom_succ, geom_zero, mul_add, add_assoc]
```
:::
::::

::::leanonly (proof := "(p : I) (k : ℕ) : geom p k = ⟦↑(σ p) ^ k * ↑p ‖ ↑(σ p) * ↑p ^ k, ↑(σ p) ^ k * ↑p, ↑(σ p) ^ (k + 1), ↑p ^ k⟧") (lemma := "geom_formula") (group := "chance.count") (uses := "geom_zero, pow_zero, one_mul, geom_succ, mul_assoc, pow_succ', pow_succ, mul_one, induction', ring, rw, simp")
:::en
*The masses.* $`k` times `false`, then `true`: the mass, as a formula.
:::

:::de
*Die Massen.* $`k`-mal `false`, dann `true`: die Masse, als Formel.
:::

:::proofen
Induction on $`k`; `pow_succ' : a ^ (n + 1) = a * a ^ n` and `mul_assoc` (read backwards).
:::

:::proofde
Induktion über $`k`; `pow_succ' : a ^ (n + 1) = a * a ^ n` und `mul_assoc` (rückwärts).
:::
:::solution
```
induction' k with k ih
rw [geom_zero, pow_zero, one_mul]
rw [geom_succ, ih, ← mul_assoc, ← pow_succ']
```
:::
:::solution
```
induction' k with k ih
rw [geom_zero, pow_zero, one_mul]
rw [geom_succ, ih]
ring
```
:::
:::solution
```
induction' k with k ih
rw [geom_zero, pow_zero, one_mul]
rw [geom_succ, ih, pow_succ', mul_assoc]
```
:::
:::solution
```
induction' k with k ih
simp [geom_zero]
rw [geom_succ, ih, ← mul_assoc, ← pow_succ']
```
:::
::::

:::::leanonly (proof := "(p : I) (k m : ℕ) : geom p (k + m) = ⟦↑(σ p) ^ k ‖ ↑(σ p) ^ m, ↑p ^ k, ↑(σ p) ^ k, geom p k⟧ * geom p m") (lemma := "geom_memoryless") (group := "chance.count") (uses := "zero_add, pow_zero, one_mul, add_right_comm, geom_succ, mul_assoc, pow_succ', geom_formula, add_assoc, add_comm, add_zero, mul_zero, pow_succ, mul_one, geom_zero, induction', ring, rw")
::::hint (anchor := "item:geom_succ")
:::en
`geom_succ` needs `geom p (n + 1)`: first `add_right_comm` turns `k + 1 + m` into `k + m + 1`.
:::

:::de
`geom_succ` braucht `geom p (n + 1)`: Erst macht `add_right_comm` aus `k + 1 + m` ein `k + m + 1`.
:::
::::

:::en
*Without memory.* $`k` times `false` first, and then as if nothing had happened: the coin does not remember.
:::

:::de
*Ohne Gedächtnis.* Erst $`k`-mal `false`, und dann, als wäre nichts gewesen: Die Münze erinnert sich nicht.
:::

:::proofen
Induction on $`k`; `add_right_comm` brings `k + 1 + m` into the form `k + m + 1`.
:::

:::proofde
Induktion über $`k`; `add_right_comm` bringt `k + 1 + m` in die Form `k + m + 1`.
:::
:::solution
```
induction' k with k ih
rw [zero_add, pow_zero, one_mul]
rw [add_right_comm, geom_succ, ih, ← mul_assoc, ← pow_succ']
```
:::
:::solution
```
rw [geom_formula, geom_formula]
ring
```
:::
:::solution
```
induction' k with k ih
rw [zero_add, pow_zero, one_mul]
rw [add_right_comm, geom_succ, ih]
ring
```
:::
:::solution
```
induction' k with k ih
rw [zero_add, pow_zero, one_mul]
rw [add_assoc, add_comm 1 m, ← add_assoc, geom_succ, ih, ← mul_assoc, ← pow_succ']
```
:::
:::::

::::leanonly (proof := "(p : I) : ∑' k, (↑(σ p) : ℝ≥0∞) ^ k = (↑p)⁻¹") (new := "ENNReal.tsum_geometric, one_sub_symm") (group := "chance.count") (uses := "ENNReal.tsum_geometric, one_sub_symm, rw, simp")
:::en
*A geometric series.* $`\sum_k (1 - p)^k = 1 / p`. `∑' k, a k` is the sum over all $`k`, as a mass (it may be $`\infty`: for $`p = 0`).
:::

:::de
*Eine geometrische Reihe.* $`\sum_k (1 - p)^k = 1 / p`. `∑' k, a k` ist die Summe über alle $`k`, als Masse (sie darf $`\infty` sein: für $`p = 0`).
:::

:::proofen
`ENNReal.tsum_geometric : ∑' k, r ^ k = (1 - r)⁻¹`, and `one_sub_symm : 1 - ↑(σ p) = ↑p`.
:::

:::proofde
`ENNReal.tsum_geometric : ∑' k, r ^ k = (1 - r)⁻¹` und `one_sub_symm : 1 - ↑(σ p) = ↑p`.
:::
:::solution
```
rw [ENNReal.tsum_geometric, one_sub_symm]
```
:::
:::solution
```
simp [ENNReal.tsum_geometric, one_sub_symm]
```
:::
:::solution
```
rw [ENNReal.tsum_geometric]
simp [one_sub_symm]
```
:::
::::

::::leanonly (proof := "(p : I) : ∑' k, (↑(σ p) : ℝ≥0∞) ^ k * ↑p = (↑p : ℝ≥0∞)⁻¹ * ↑p") (new := "ENNReal.tsum_mul_right") (group := "chance.count") (uses := "ENNReal.tsum_mul_right, ENNReal.tsum_geometric, one_sub_symm, rw, simp")
:::en
*Factoring out.* A factor that does not depend on $`k` comes out of the sum.
:::

:::de
*Ausklammern.* Ein Faktor, der nicht von $`k` abhängt, kommt aus der Summe heraus.
:::

:::proofen
`ENNReal.tsum_mul_right : ∑' k, f k * a = (∑' k, f k) * a`.
:::

:::proofde
`ENNReal.tsum_mul_right : ∑' k, f k * a = (∑' k, f k) * a`.
:::
:::solution
```
rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, one_sub_symm]
```
:::
:::solution
```
rw [ENNReal.tsum_mul_right]
simp [one_sub_symm]
```
:::
:::solution
```
simp [ENNReal.tsum_mul_right, one_sub_symm]
```
:::
::::

:::::leanonly (proof := "(p : I) (h : p ≠ 0) : ∑' k, geom p k = 1") (new := "ENNReal.inv_mul_cancel, mass_ne_zero, mass_finite") (group := "chance.count") (uses := "geom_formula, ENNReal.tsum_mul_right, ENNReal.tsum_geometric, one_sub_symm, ENNReal.inv_mul_cancel, mass_ne_zero, mass_finite, apply, exact, rw, simp, simp_rw")
::::hint (anchor := "item:simp_rw")
:::en
`rw` does not rewrite under `∑' k`, where `k` is a bound name; `simp_rw` does.
:::

:::de
`rw` schreibt nicht unter `∑' k` um, wo `k` ein gebundener Name ist; `simp_rw` schon.
:::
::::

:::en
*Total mass one.* If $`p \neq 0`, the first `true` comes for sure: the masses add up to one. (For $`p = 0` it never comes, and all masses are $`0`.)
:::

:::de
*Gesamtmasse eins.* Wenn $`p \neq 0`, kommt das erste `true` sicher: Die Massen ergeben zusammen eins. (Für $`p = 0` kommt es nie, und alle Massen sind $`0`.)
:::

:::proofen
Your formula under the sum (`simp_rw`, it rewrites under `∑'`), the last level, and `ENNReal.inv_mul_cancel (h₀ : a ≠ 0) (h₁ : a ≠ ⊤) : a⁻¹ * a = 1`, with `mass_ne_zero h : ↑p ≠ 0` and `mass_finite p : ↑p ≠ ⊤`.
:::

:::proofde
Deine Formel unter der Summe (`simp_rw`, es schreibt unter `∑'` um), das letzte Level, und `ENNReal.inv_mul_cancel (h₀ : a ≠ 0) (h₁ : a ≠ ⊤) : a⁻¹ * a = 1`, mit `mass_ne_zero h : ↑p ≠ 0` und `mass_finite p : ↑p ≠ ⊤`.
:::
:::solution
```
simp_rw [geom_formula]
rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, one_sub_symm]
rw [ENNReal.inv_mul_cancel (mass_ne_zero h) (mass_finite p)]
```
:::
:::solution
```
simp_rw [geom_formula]
rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, one_sub_symm]
apply ENNReal.inv_mul_cancel
exact mass_ne_zero h
exact mass_finite p
```
:::
:::solution
```
simp_rw [geom_formula]
simp [ENNReal.tsum_mul_right, one_sub_symm]
rw [ENNReal.inv_mul_cancel (mass_ne_zero h) (mass_finite p)]
```
:::
:::solution
```
simp_rw [geom_formula, ENNReal.tsum_mul_right, ENNReal.tsum_geometric, one_sub_symm]
rw [ENNReal.inv_mul_cancel (mass_ne_zero h) (mass_finite p)]
```
:::
:::::

::::leanonly (proof := "(p : I) : geom p = (do let x ← coin p; bif x then pure 0 else (do let Y ← geom p; pure (1 + Y)))") (lemma := "geom_first") (group := "chance.count") (uses := "coin_bind_apply, Bool.cond_true, Bool.cond_false, pure_self, shift_zero, mul_zero, add_zero, mul_one, geom_zero, pure_zero_succ, shift_succ, zero_add, geom_succ, one_mul, <;>, cases, ext, rw, simp")
:::en
*Boss: waiting for the first true.* Throw once: on `true` it is $`0`; on `false`, start again, and add one. The geometric distribution is the one that does this: it is defined by its masses, and here it is a `do` block that calls itself.
:::

:::de
*Endgegner: Warten auf das erste true.* Wirf einmal: Bei `true` ist es $`0`; bei `false` fang von vorne an, und zähl eins dazu. Die geometrische Verteilung ist die, die das tut: Sie ist durch ihre Massen definiert, und hier ist sie ein `do`-Block, der sich selbst aufruft.
:::
:::solution
```
ext k
cases k
rw [coin_bind_apply, Bool.cond_true, Bool.cond_false, pure_self, shift_zero, mul_zero, add_zero, mul_one, geom_zero]
rw [coin_bind_apply, Bool.cond_true, Bool.cond_false, pure_zero_succ, shift_succ, mul_zero, zero_add, geom_succ]
```
:::
:::solution
```
ext k
cases k <;> simp [geom_zero, geom_succ]
```
:::
:::solution
```
ext k
cases k
simp [geom_zero]
simp [geom_succ]
```
:::
:::solution
```
ext k
rw [coin_bind_apply, Bool.cond_true, Bool.cond_false]
cases k
rw [pure_self, shift_zero, mul_one, mul_zero, add_zero, geom_zero]
rw [pure_zero_succ, shift_succ, mul_zero, zero_add, geom_succ]
```
:::
::::
