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

/-- Flipping a coin: `not` swaps the masses `p` and `1 - p`. -/
theorem coin_not (p : I) : not <$> coin p = coin (σ p) := by
  rw [← MeasureTheory.DiscreteMeasure.map_eq_map]; exact MeasureTheory.DiscreteMeasure.coin_not' p

/-- A coin whose result is not used changes nothing. -/
theorem coin_unused {β : Type} (p : I) (ν : DiscreteMeasure β) : (do let _ ← coin p; ν) = ν :=
  MeasureTheory.DiscreteMeasure.bind_const_of_hasSum (MeasureTheory.DiscreteMeasure.hasSum_coin p) ν

/-- A constant map sends all the sand to one point. -/
theorem coin_const {β : Type} (p : I) (b : β) : (fun _ => b) <$> coin p = pure b := by
  rw [← bind_pure_comp]; exact coin_unused p _

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

/-! The lemmas the player proves (world 3); the game unlocks each after its level. -/

/-- World 3, level 2: `B(1, p)` is a coin as a number. -/
theorem binom_one (p : I) : Bool.toNat <$> coin p = binom p 1 := by
  rw [binom_succ, binom_zero]
  simp only [pure_bind, add_zero]
  rw [map_eq_pure_bind]

/-- World 3, level 3: one throw more, at the end. -/
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
