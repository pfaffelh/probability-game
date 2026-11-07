import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# World 1, one coin: the statements of the levels, for every `p`

Checked against Mathlib by `./check-proofs.sh` (it runs `lake env lean` in a project with Mathlib).
The boss (level 8) is `bernoulli_not` of `Journal/Notes/DoProbability.lean`.
-/

open PMF
open scoped NNReal ENNReal

namespace ProbGame.OneCoin

variable (p : ℝ≥0) (h : p ≤ 1)

/-- Level 1: flipped twice, the same coin. -/
theorem flip_flip : ((bernoulli p h).map not).map not = bernoulli p h := by
  rw [map_comp]
  have : (not ∘ not) = id := funext Bool.not_not
  rw [this, map_id]

/-- Level 2: flipped, the mass at `true` is `1 - p`. -/
theorem flip_true : (bernoulli p h).map not true = 1 - p := by
  simp [map_apply, bernoulli_apply, tsum_bool, ENNReal.coe_sub]

/-- Level 3: always heads, a point mass. -/
theorem always_heads : (bernoulli p h).map (fun _ => true) = pure true := map_const _ _

/-- Level 4: surely tails, by always heads and then a flip. -/
theorem tails_by_heads : ((bernoulli p h).map (fun _ => true)).map not = pure false := by
  rw [map_comp]
  exact map_const _ _

/-- Level 5: heads as 1, tails as 0. -/
theorem to_nat : (bernoulli p h).map Bool.toNat 1 = p := by
  simp [map_apply, bernoulli_apply, tsum_bool]

/-- Level 6: a bet, heads wins 5, tails loses 2. -/
theorem bet : (bernoulli p h).map (fun b => if b then (5 : ℤ) else -2) 5 = p := by
  simp [map_apply, bernoulli_apply, tsum_bool]

/-- Level 7: surely zero. -/
theorem surely_zero : ((bernoulli p h).map (fun _ => false)).map Bool.toNat = pure 0 := by
  rw [map_comp]
  exact map_const _ _

/-- Level 8, the boss: flip the coin. -/
theorem flip : (bernoulli p h).map not = bernoulli (1 - p) tsub_le_self := by
  ext b
  cases b <;> simp [map_apply, bernoulli_apply, tsum_bool, ENNReal.coe_sub]
  exact (ENNReal.sub_sub_cancel ENNReal.one_ne_top (by exact_mod_cast h)).symm

/-- The image measure, in general: `P(f(X) ∈ s) = P(X ∈ f⁻¹(s))`. -/
theorem image_measure (f : Bool → Bool) (s : Set Bool) :
    ((bernoulli p h).map f).toOuterMeasure s = (bernoulli p h).toOuterMeasure (f ⁻¹' s) :=
  toOuterMeasure_map_apply _ _ _

end ProbGame.OneCoin
