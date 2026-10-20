import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# World 1, one coin: the statements of the levels, for every `p`

Checked against Mathlib by `./check-proofs.sh` (it runs `lake env lean` in a project with Mathlib).
Level 1 is `bernoulli_not` of `Journal/Notes/DoProbability.lean`.
-/

open PMF
open scoped NNReal ENNReal

namespace ProbGame.OneCoin

variable (p : ℝ≥0) (h : p ≤ 1)

/-- Level 1: flip the coin. -/
theorem flip : (bernoulli p h).map not = bernoulli (1 - p) tsub_le_self := by
  ext b
  cases b <;> simp [map_apply, bernoulli_apply, tsum_bool, ENNReal.coe_sub]
  exact (ENNReal.sub_sub_cancel ENNReal.one_ne_top (by exact_mod_cast h)).symm

/-- Level 2: always heads, a point mass. -/
theorem always_heads : (bernoulli p h).map (fun _ => true) = pure true := map_const _ _

/-- Level 3: surely tails, by always heads and then a flip. -/
theorem tails_by_heads : ((bernoulli p h).map (fun _ => true)).map not = pure false := by
  rw [map_comp]
  exact map_const _ _

/-- Level 4: heads as 1, tails as 0. -/
theorem to_nat : (bernoulli p h).map Bool.toNat 1 = p := by
  simp [map_apply, bernoulli_apply, tsum_bool]

/-- Level 5: flipped, then a number. -/
theorem flip_to_nat : ((bernoulli p h).map not).map Bool.toNat 1 = 1 - p := by
  simp [map_apply, bernoulli_apply, tsum_bool, ENNReal.coe_sub]

/-- Level 6: a bet, heads wins 5, tails loses 2. -/
theorem bet : (bernoulli p h).map (fun b => if b then (5 : ℤ) else -2) 5 = p := by
  simp [map_apply, bernoulli_apply, tsum_bool]

/-- Level 7: the better bet. -/
theorem better_bet : ((bernoulli p h).map not).map (fun b => if b then (5 : ℤ) else -2) 5 = 1 - p := by
  simp [map_apply, bernoulli_apply, tsum_bool, ENNReal.coe_sub]

/-- Level 8: surely zero. -/
theorem surely_zero : ((bernoulli p h).map (fun _ => false)).map Bool.toNat = pure 0 := by
  rw [map_comp]
  exact map_const _ _

/-- The image measure, in general: `P(f(X) ∈ s) = P(X ∈ f⁻¹(s))`. -/
theorem image_measure (f : Bool → Bool) (s : Set Bool) :
    ((bernoulli p h).map f).toOuterMeasure s = (bernoulli p h).toOuterMeasure (f ⁻¹' s) :=
  toOuterMeasure_map_apply _ _ _

end ProbGame.OneCoin
