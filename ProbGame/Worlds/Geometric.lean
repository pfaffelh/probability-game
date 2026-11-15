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
