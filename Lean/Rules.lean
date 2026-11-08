/-!
# The rules of the proof game

The context in which the levels are proved (base: `DiscreteMeasure` of the journal,
`import Journal.Notes.DiscreteMeasure.Thinning`). The player sees `coin p`, `binom p n`, `pure`,
`do` blocks and `f <$> μ`; the rules below are stated in these forms, with the monad laws of Lean's
core (`pure_bind`, `bind_pure`, `bind_assoc`, `map_pure`, `bind_map_left`, `map_bind`).

Rules that are given (the axioms of the game, as Peano's in the Natural Number Game) and lemmas
the player proves in a level are both here, proved from the journal; the game unlocks the lemmas
one after another.
-/

open MeasureTheory (DiscreteMeasure)
open MeasureTheory.DiscreteMeasure (coin binom)
open unitInterval

namespace ProbGame

/-! World 1: what a distribution on `Bool` is, and where the mass of a move goes. -/

/-- A number of `I` as a mass, written `↑p`. -/
@[coe] noncomputable def mass (p : I) : ENNReal := ENNReal.ofReal p
noncomputable instance : CoeTC I ENNReal := ⟨mass⟩

/-- `μ` is a distribution: its total mass is one. -/
class Prob {α : Type} (μ : DiscreteMeasure α) : Prop where
  hasSum : HasSum μ.weight 1

instance (p : I) : Prob (coin p) := ⟨MeasureTheory.DiscreteMeasure.hasSum_coin p⟩
instance {α β : Type} (μ : DiscreteMeasure α) [h : Prob μ] (f : α → β) : Prob (f <$> μ) :=
  ⟨MeasureTheory.DiscreteMeasure.hasSum_map h.hasSum f⟩
instance {α : Type} (a : α) : Prob (pure a : DiscreteMeasure α) := ⟨MeasureTheory.DiscreteMeasure.hasSum_pure a⟩

/-- The mass of a coin at `true`. -/
theorem coin_true (p : I) : coin p true = p := MeasureTheory.DiscreteMeasure.coin_apply_true p

/-- The mass of a coin at `false`. -/
theorem coin_false (p : I) : coin p false = σ p := MeasureTheory.DiscreteMeasure.coin_apply_false p

/-- The total mass of a coin is one. -/
theorem coin_total (p : I) : coin p true + coin p false = 1 := by
  have := (MeasureTheory.DiscreteMeasure.hasSum_coin p).tsum_eq
  rw [tsum_fintype, Fintype.sum_bool] at this; exact this

/-- The mass of a point mass at `true`: one if it sits there, else zero. -/
theorem pure_true (b : Bool) : (pure b : DiscreteMeasure Bool) true = bif b then 1 else 0 := by
  cases b
  · exact MeasureTheory.DiscreteMeasure.pure_apply_nonself (by decide)
  · exact MeasureTheory.DiscreteMeasure.pure_apply_self

/-- Two distributions on `Bool` are the same when they have the same mass at `true`: the rest of
the mass lies at `false`. -/
theorem bool_ext (μ ν : DiscreteMeasure Bool) [hμ : Prob μ] [hν : Prob ν] (h : μ true = ν true) : μ = ν := by
  have a := hμ.hasSum.tsum_eq; have b := hν.hasSum.tsum_eq
  rw [tsum_fintype, Fintype.sum_bool] at a b
  simp only [MeasureTheory.DiscreteMeasure.weight_eq] at a b
  have ht : μ true ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (a ▸ le_self_add)
  ext x; cases x
  · rw [h] at a ht
    exact (ENNReal.add_right_inj ht).1 (a.trans b.symm)
  · exact h

/-- Where the mass of a move goes: the mass of `f <$> μ` at `true` is the mass of `μ` at the points
that `f` sends to `true` (`bif c then a else b` is `a` when `c` is `true`, else `b`). -/
theorem map_true (f : Bool → Bool) (μ : DiscreteMeasure Bool) :
    (f <$> μ) true = (bif f true then μ true else 0) + (bif f false then μ false else 0) := by
  rw [← MeasureTheory.DiscreteMeasure.map_eq_map, MeasureTheory.DiscreteMeasure.map_apply_eq_tsum_mul,
    tsum_fintype, Fintype.sum_bool]
  cases f true <;> cases f false <;> simp [Set.indicator]

/-- A coin whose result is not used changes nothing. -/
theorem coin_unused {β : Type} (p : I) (ν : DiscreteMeasure β) : (do let _ ← coin p; ν) = ν :=
  MeasureTheory.DiscreteMeasure.bind_const_of_hasSum (MeasureTheory.DiscreteMeasure.hasSum_coin p) ν

/-- Two moves are one move. -/
theorem map_map {α β γ : Type} (μ : DiscreteMeasure α) (f : α → β) (g : β → γ) :
    g <$> (f <$> μ) = (fun x => g (f x)) <$> μ := (comp_map f g μ).symm

/-- Independence: two coins, both `true`, is a coin `p * q`. -/
theorem coin_and (p q : I) : (do let x ← coin p; let y ← coin q; pure (x && y)) = coin (p * q) := by
  rw [← MeasureTheory.DiscreteMeasure.twoCoins_and_eq_coin]
  simp only [map_eq_pure_bind, seq_eq_bind_map, bind_assoc, pure_bind]

/-- Independence: the order of two independent draws does not matter. -/
theorem bind_comm {α β γ : Type} (μ : DiscreteMeasure α) (ν : DiscreteMeasure β) (f : α → β → DiscreteMeasure γ) :
    (do let x ← μ; let y ← ν; f x y) = (do let y ← ν; let x ← μ; f x y) :=
  MeasureTheory.DiscreteMeasure.bind_comm μ ν f

/-- De Morgan. -/
theorem or_eq (x y : Bool) : (x || y) = !(!x && !y) := by cases x <;> cases y <;> rfl

/-- The binomial distribution, by its definition: no throw. -/
theorem binom_zero (p : I) : binom p 0 = pure 0 := rfl

/-- The binomial distribution, by its definition: one throw more. -/
theorem binom_succ (p : I) (n : ℕ) :
    binom p (n + 1) = (do let X ← coin p; let Y ← binom p n; pure (X.toNat + Y)) := rfl

/-! The lemmas the player proves; the game unlocks each after its level. -/

/-- One Coin, level 1: flipped, the coin has the mass `1 - p` at `true`. -/
theorem coin_not_true (p : I) : (not <$> coin p) true = σ p := by
  rw [map_true]
  rw [Bool.not_true, Bool.not_false]
  rw [Bool.cond_false, Bool.cond_true, zero_add]
  rw [coin_false]

/-- One Coin, level 2: a constant move sends all the mass to one point. -/
theorem coin_const (p : I) (b : Bool) : (fun _ => b) <$> coin p = pure b := by
  apply bool_ext
  rw [map_true, pure_true]
  cases b
  rw [Bool.cond_false, Bool.cond_false, Bool.cond_false, zero_add]
  rw [Bool.cond_true, Bool.cond_true, Bool.cond_true, coin_total]

/-- World 1, the boss: flipping a coin swaps the masses `p` and `1 - p`. -/
theorem coin_not (p : I) : not <$> coin p = coin (σ p) := by
  apply bool_ext
  rw [coin_not_true, coin_true]

/-- `B(1, p)` is a coin as a number. -/
theorem binom_one (p : I) : Bool.toNat <$> coin p = binom p 1 := by
  rw [binom_succ, binom_zero]
  simp only [pure_bind, add_zero]
  rw [map_eq_pure_bind]

/-- Counting, level 2: one throw more, at the end. -/
theorem binom_succ' (p : I) (n : ℕ) :
    (do let X ← binom p n; let Y ← coin p; pure (X + Y.toNat)) = binom p (n + 1) := by
  induction' n with n ih
  · rw [binom_zero, binom_succ, binom_zero]
    simp only [pure_bind, zero_add, add_zero]
  · rw [binom_succ p n, binom_succ p (n + 1), ← ih]
    simp only [bind_assoc, pure_bind, add_assoc]

/-- World 3, the boss: the sum of independent binomials. -/
theorem binom_add (p : I) (n m : ℕ) :
    (do let X ← binom p n; let Y ← binom p m; pure (X + Y)) = binom p (n + m) := by
  induction' m with m ih
  · rw [binom_zero]
    simp only [pure_bind, add_zero, bind_pure]
  · rw [← binom_succ' p m, ← add_assoc, ← binom_succ' p (n + m), ← ih]
    simp only [bind_assoc, pure_bind, add_assoc]

end ProbGame

open ProbGame
