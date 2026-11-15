import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Geometric" =>

%%%
htmlSplit := .never
%%%

:::en
How long until the first `true`? The geometric distribution, defined by its masses step by step; its formula, its lack of memory, and the `do` block that waits. In Lean only.
:::

:::de
Wie lange bis zum ersten `true`? Die geometrische Verteilung, Schritt für Schritt durch ihre Massen definiert; ihre Formel, ihre Gedächtnislosigkeit, und der `do`-Block, der wartet. Nur in Lean.
:::

::::leanonly (proof := "(p : I) : geom p 0 = ↑p") (lemma := "geom_zero") (group := "chance.count")
:::en
*True at once.* Throw a coin `p` until it shows `true`; `geom p` is the number of `false` before. Its masses are defined step by step: at once `true`, mass $`p`; one `false` more, $`1 - p` times as much.
:::

:::de
*Sofort true.* Wirf eine Münze `p`, bis sie `true` zeigt; `geom p` ist die Anzahl der `false` davor. Ihre Massen sind Schritt für Schritt definiert: sofort `true`, Masse $`p`; ein `false` mehr, $`1 - p`-mal so viel.
:::

:::proofen
The definition:

```
def geomMass (p : I) : ℕ → ENNReal
  | 0 => ↑p
  | k + 1 => ↑(σ p) * geomMass p k

def geom (p : I) : DiscreteMeasure ℕ := ⟨geomMass p⟩
```

The first case.

*Tip.* `rfl`.
:::

:::proofde
Die Definition:

```
def geomMass (p : I) : ℕ → ENNReal
  | 0 => ↑p
  | k + 1 => ↑(σ p) * geomMass p k

def geom (p : I) : DiscreteMeasure ℕ := ⟨geomMass p⟩
```

Der erste Fall.

*Tipp.* `rfl`.
:::
:::solution
```
rfl
```
:::
::::

::::leanonly (proof := "(p : I) (k : ℕ) : geom p (k + 1) = ↑(σ p) * geom p k") (lemma := "geom_succ") (group := "chance.count")
:::en
*One false more.* The second case of the definition.
:::

:::de
*Ein false mehr.* Der zweite Fall der Definition.
:::

:::proofen
By definition.

*Tip.* `rfl`.
:::

:::proofde
Nach Definition.

*Tipp.* `rfl`.
:::
:::solution
```
rfl
```
:::
::::

::::leanonly (proof := "(p : I) (k : ℕ) : geom p k = ↑(σ p) ^ k * ↑p") (lemma := "geom_formula") (new := "pow_succ', mul_assoc") (group := "chance.count")
:::en
*The masses.* $`k` times `false`, then `true`: mass $`(1 - p)^k p`.
:::

:::de
*Die Massen.* $`k`-mal `false`, dann `true`: Masse $`(1 - p)^k p`.
:::

:::proofen
Induction on $`k`; `pow_succ' : a ^ (n + 1) = a * a ^ n` and `mul_assoc` (read backwards).

*Tip.* `induction' k with k ih`; `rw [geom_zero, pow_zero, one_mul]`; `rw [geom_succ, ih, ← mul_assoc, ← pow_succ']`.
:::

:::proofde
Induktion über $`k`; `pow_succ' : a ^ (n + 1) = a * a ^ n` und `mul_assoc` (rückwärts).

*Tipp.* `induction' k with k ih`; `rw [geom_zero, pow_zero, one_mul]`; `rw [geom_succ, ih, ← mul_assoc, ← pow_succ']`.
:::
:::solution
```
induction' k with k ih
rw [geom_zero, pow_zero, one_mul]
rw [geom_succ, ih, ← mul_assoc, ← pow_succ']
```
:::
::::

::::leanonly (proof := "(p : I) (k m : ℕ) : geom p (k + m) = ↑(σ p) ^ k * geom p m") (lemma := "geom_memoryless") (group := "chance.count")
:::en
*Without memory.* $`k` times `false` first, and then as if nothing had happened: the coin does not remember.
:::

:::de
*Ohne Gedächtnis.* Erst $`k`-mal `false`, und dann, als wäre nichts gewesen: Die Münze erinnert sich nicht.
:::

:::proofen
Induction on $`k`; `add_right_comm` brings `k + 1 + m` into the form `k + m + 1`.

*Tip.* `induction' k with k ih`; `rw [zero_add, pow_zero, one_mul]`; `rw [add_right_comm, geom_succ, ih, ← mul_assoc, ← pow_succ']`.
:::

:::proofde
Induktion über $`k`; `add_right_comm` bringt `k + 1 + m` in die Form `k + m + 1`.

*Tipp.* `induction' k with k ih`; `rw [zero_add, pow_zero, one_mul]`; `rw [add_right_comm, geom_succ, ih, ← mul_assoc, ← pow_succ']`.
:::
:::solution
```
induction' k with k ih
rw [zero_add, pow_zero, one_mul]
rw [add_right_comm, geom_succ, ih, ← mul_assoc, ← pow_succ']
```
:::
::::

::::leanonly (proof := "(p : I) : geom p = (do let x ← coin p; bif x then pure 0 else (do let Y ← geom p; pure (1 + Y)))") (lemma := "geom_first") (group := "chance.count")
:::en
*Boss: waiting for the first true.* Throw once: on `true` it is $`0`; on `false`, start again, and add one. The geometric distribution is the one that does this: it is defined by its masses, and here it is a `do` block that calls itself.
:::

:::de
*Endgegner: Warten auf das erste true.* Wirf einmal: Bei `true` ist es $`0`; bei `false` fang von vorne an, und zähl eins dazu. Die geometrische Verteilung ist die, die das tut: Sie ist durch ihre Massen definiert, und hier ist sie ein `do`-Block, der sich selbst aufruft.
:::

:::proofen
Two distributions on `ℕ` are the same when they have the same mass at every `k`: `ext k`. Then `k` is `0` or `k + 1`: `cases k`. The rules of *Binomial* do the rest.

*Tip.* `ext k`, `cases k`; at `0`: `rw [coin_bind_apply, Bool.cond_true, Bool.cond_false, pure_self, shift_zero, mul_zero, add_zero, mul_one, geom_zero]`; at `k + 1`: `rw [coin_bind_apply, Bool.cond_true, Bool.cond_false, pure_zero_succ, shift_succ, mul_zero, zero_add, geom_succ]`.
:::

:::proofde
Zwei Verteilungen auf `ℕ` sind gleich, wenn sie an jedem `k` dieselbe Masse haben: `ext k`. Dann ist `k` gleich `0` oder `k + 1`: `cases k`. Die Regeln aus *Binomial* erledigen den Rest.

*Tipp.* `ext k`, `cases k`; bei `0`: `rw [coin_bind_apply, Bool.cond_true, Bool.cond_false, pure_self, shift_zero, mul_zero, add_zero, mul_one, geom_zero]`; bei `k + 1`: `rw [coin_bind_apply, Bool.cond_true, Bool.cond_false, pure_zero_succ, shift_succ, mul_zero, zero_add, geom_succ]`.
:::
:::solution
```
ext k
cases k
rw [coin_bind_apply, Bool.cond_true, Bool.cond_false, pure_self, shift_zero, mul_zero, add_zero, mul_one, geom_zero]
rw [coin_bind_apply, Bool.cond_true, Bool.cond_false, pure_zero_succ, shift_succ, mul_zero, zero_add, geom_succ]
```
:::
::::
