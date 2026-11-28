/-!
# The rules of the proof game

The context in which the levels are proved (base: `DiscreteMeasure` of the journal,
`import Journal.Notes.DiscreteMeasure.Thinning`). The player sees `coin p`, `binom p n`, `pure`,
`do` blocks and `μ.map f`; the rules below are stated in these forms, with the monad laws of Lean's
core (`pure_bind`, `bind_pure`, `bind_assoc`) and those of a move, stated here with `μ.map f`
(`map_pure`, `bind_map_left`, `map_bind`, `map_map`).

Rules that are given (the axioms of the game, as Peano's in the Natural Number Game) and lemmas
the player proves in a level are both here, proved from the journal; the game unlocks the lemmas
one after another.
-/

open MeasureTheory (DiscreteMeasure)
open MeasureTheory.DiscreteMeasure (coin binom iidSequence)
open unitInterval
open scoped ENNReal

/-- A move is printed as the game writes it: `μ.map f`, not `DiscreteMeasure.map f μ`. -/
@[app_unexpander MeasureTheory.DiscreteMeasure.map]
def ProbGame.unexpandMap : Lean.PrettyPrinter.Unexpander
  | `($_ $f $μ:ident) => `($(Lean.mkIdent (μ.getId ++ `map)) $f)
  | `($_ $f $μ) => `(($μ).$(Lean.mkIdent `map):ident $f)
  | _ => throw ()

/-- The names in a piece of syntax (for `unexpandBind`). -/
partial def ProbGame.namesIn : Lean.Syntax → List Lean.Name
  | .ident _ _ n _ => [n]
  | .node _ _ args => args.toList.flatMap ProbGame.namesIn
  | _ => []

/-- A bind is printed as the game writes it, as a `do` block, also where the function after it is not
written out: `μ >>= f`, `μ >>= pure`, or a hole `?f` in a message of Lean (a `fun` Lean prints as a
`do` block itself). The draw gets a name that `μ` and `f` do not use. -/
@[app_unexpander Bind.bind]
def ProbGame.unexpandBind : Lean.PrettyPrinter.Unexpander
  | `($_ $m $f) => do
    if f.raw.isOfKind ``Lean.Parser.Term.fun then throw ()
    let names := ProbGame.namesIn m.raw ++ ProbGame.namesIn f.raw
    let x := Lean.mkIdent <| ([`x, `y, `z, `a, `b, `c].find? (!names.contains ·)).getD `x
    let body ← `($f $x)
    `(do
        let $x:ident ← $m:term
        $body:term)
  | _ => throw ()

/-- A functor map is printed as the game writes a move: `μ.map f`, not `f <$> μ`. -/
@[app_unexpander Functor.map]
def ProbGame.unexpandFunctorMap : Lean.PrettyPrinter.Unexpander
  | `($_ $f $μ:ident) => `($(Lean.mkIdent (μ.getId ++ `map)) $f)
  | `($_ $f $μ) => `(($μ).$(Lean.mkIdent `map):ident $f)
  | _ => throw ()

namespace ProbGame

/-! World 1: what a distribution on `Bool` is, and where the mass of a move goes. -/

/-- A number of `I` as a mass, written `↑p`. -/
@[coe] noncomputable def mass (p : I) : ENNReal := ENNReal.ofReal p
noncomputable instance : CoeTC I ENNReal := ⟨mass⟩

/-- `μ` is a distribution: its total mass is one. -/
class Prob {α : Type} (μ : DiscreteMeasure α) : Prop where
  hasSum : HasSum μ.weight 1

instance (p : I) : Prob (coin p) := ⟨MeasureTheory.DiscreteMeasure.hasSum_coin p⟩
instance {α β : Type} (μ : DiscreteMeasure α) [h : Prob μ] (f : α → β) : Prob (μ.map f) :=
  ⟨MeasureTheory.DiscreteMeasure.hasSum_map h.hasSum f⟩
instance {α : Type} (a : α) : Prob (pure a : DiscreteMeasure α) := ⟨MeasureTheory.DiscreteMeasure.hasSum_pure a⟩
instance {α β : Type} (μ : DiscreteMeasure α) [h : Prob μ] (f : α → DiscreteMeasure β) [hf : ∀ a, Prob (f a)] :
    Prob (μ >>= f) :=
  ⟨MeasureTheory.DiscreteMeasure.hasSum_bind h.hasSum (fun a _ => (hf a).hasSum)⟩
instance {α : Type} (c : Bool) (μ ν : DiscreteMeasure α) [h : Prob μ] [h' : Prob ν] :
    Prob (bif c then μ else ν) := by
  cases c
  · exact h'
  · exact h

/-- The mass of a coin at `true`. -/
theorem coin_true (p : I) : coin p true = p := MeasureTheory.DiscreteMeasure.coin_apply_true p

/-- The mass of a coin at `false`. -/
theorem coin_false (p : I) : coin p false = σ p := MeasureTheory.DiscreteMeasure.coin_apply_false p

/-- The total mass of a coin is one. -/
theorem coin_total (p : I) : coin p true + coin p false = 1 := by
  have := (MeasureTheory.DiscreteMeasure.hasSum_coin p).tsum_eq
  rw [tsum_fintype, Fintype.sum_bool] at this; exact this

/-- The definition of a point mass, as the game writes it: mass one at its point, zero elsewhere. -/
theorem pure_apply {α : Type} [DecidableEq α] (a b : α) :
    (pure a : DiscreteMeasure α) b = bif a == b then 1 else 0 := by
  by_cases h : a = b
  · subst h; simp; exact MeasureTheory.DiscreteMeasure.pure_apply_self
  · simp [h]; exact MeasureTheory.DiscreteMeasure.pure_apply_nonself (Ne.symm h)

/-- The mass of a point mass at `true`: one if it sits there, else zero. -/
theorem pure_true (b : Bool) : (pure b : DiscreteMeasure Bool) true = bif b then 1 else 0 := by
  cases b
  · exact MeasureTheory.DiscreteMeasure.pure_apply_nonself (by decide)
  · exact MeasureTheory.DiscreteMeasure.pure_apply_self

/-- The mass of a point mass at `false`: zero if it sits at `true`, else one. -/
theorem pure_false (b : Bool) : (pure b : DiscreteMeasure Bool) false = bif b then 0 else 1 := by
  rw [pure_apply]; cases b <;> rfl

/-- What `Prob μ` says: the masses of `μ`, summed over all points, give one. -/
theorem Prob.total {α : Type} (μ : DiscreteMeasure α) [h : Prob μ] : ∑' a, μ a = 1 :=
  h.hasSum.tsum_eq

/-- The total mass of a distribution on `Bool` is one. -/
theorem mass_total (μ : DiscreteMeasure Bool) [hμ : Prob μ] : μ true + μ false = 1 := by
  have a := hμ.hasSum.tsum_eq
  rw [tsum_fintype, Fintype.sum_bool] at a
  simpa only [MeasureTheory.DiscreteMeasure.weight_eq] using a

/-- A mass of a distribution on `Bool` is at most one. -/
theorem mass_le_one (μ : DiscreteMeasure Bool) [Prob μ] (b : Bool) : μ b ≤ 1 := by
  rw [← mass_total μ]
  cases b
  · exact le_add_self
  · exact le_self_add

/-- A mass of a distribution is finite (at most one). -/
theorem mass_ne_top {μ : DiscreteMeasure Bool} [Prob μ] {b : Bool} : μ b ≠ ⊤ := by
  cases b
  · exact ne_top_of_le_ne_top ENNReal.one_ne_top ((mass_total μ) ▸ le_add_self)
  · exact ne_top_of_le_ne_top ENNReal.one_ne_top ((mass_total μ) ▸ le_self_add)

/-- One Coin, *The rest of the mass*: what is not at `b` lies at `!b`. -/
theorem mass_not (μ : DiscreteMeasure Bool) [Prob μ] (b : Bool) : μ b = 1 - μ (!b) := by
  cases b
  · rw [Bool.not_false, ← mass_total μ, ENNReal.add_sub_cancel_left mass_ne_top]
  · rw [Bool.not_true, ← mass_total μ, add_comm, ENNReal.add_sub_cancel_left mass_ne_top]

/-- One Coin, *One bar is enough*: two distributions on `Bool` are the same when they have the
same mass at `true`. -/
theorem bool_ext (μ ν : DiscreteMeasure Bool) [Prob μ] [Prob ν] (h : μ true = ν true) : μ = ν := by
  ext x
  cases x
  · rw [mass_not μ false, mass_not ν false, Bool.not_false, h]
  · exact h

-- The masses of coins and point masses are computing, not rules of the game: `norm_num` (in the
-- inventory from *Building with Coins* on) knows them.
attribute [simp] coin_true coin_false pure_true pure_false

/-- $`p + (1 - p) = 1`, as masses: computing for `norm_num`. -/
@[simp] theorem add_symm_eq_one (p : I) : (↑p : ENNReal) + ↑(σ p) = 1 := by
  rw [← coin_true, ← coin_false, coin_total]

/-- The definition of a move on `Bool`, as the game writes it: the mass of `μ.map f` at `b` is the
sum of the masses `μ a` of the points `a` that `f` sends to `b` (the image measure, `μ ∘ f⁻¹`). -/
theorem map_apply (f : Bool → Bool) (μ : DiscreteMeasure Bool) (b : Bool) :
    (μ.map f) b = ∑ a with f a = b, μ a := by
  rw [MeasureTheory.DiscreteMeasure.map_apply_eq_tsum_mul, tsum_fintype, Finset.sum_filter]
  congr 1
  funext a
  by_cases h : f a = b <;> simp [Set.indicator, h]

/-- A sum over the points with `f a = b`, as a sum over all points with a test. -/
theorem sum_with {α : Type} [Fintype α] (f : α → Bool) (b : Bool) (g : α → ℝ≥0∞) :
    (∑ a with f a = b, g a) = ∑ a, (bif f a == b then g a else 0) := by
  rw [Finset.sum_filter]
  congr 1
  funext a
  cases h : f a <;> cases b <;> simp

/-- A move on `Bool`, written out (proved by the player in *Masses*): to `b` comes the mass at
`true` when `f true` is `b`, and the mass at `false` when `f false` is `b`. -/
theorem map_bool (f : Bool → Bool) (μ : DiscreteMeasure Bool) (b : Bool) :
    (μ.map f) b = (bif f true == b then μ true else 0) + (bif f false == b then μ false else 0) := by
  rw [map_apply, sum_with, Fintype.sum_bool]

/-- Where the mass of a move goes: the mass of `μ.map f` at `true` is the mass of `μ` at the points
that `f` sends to `true` (`bif c then a else b` is `a` when `c` is `true`, else `b`). -/
theorem map_true (f : Bool → Bool) (μ : DiscreteMeasure Bool) :
    (μ.map f) true = (bif f true then μ true else 0) + (bif f false then μ false else 0) := by
  rw [MeasureTheory.DiscreteMeasure.map_apply_eq_tsum_mul,
    tsum_fintype, Fintype.sum_bool]
  cases f true <;> cases f false <;> simp [Set.indicator]

/-- The boss of *DiscreteMeasure*: `not` brings the mass at `false` to `true`. -/
theorem map_not_true (μ : DiscreteMeasure Bool) : (μ.map not) true = μ false := by
  rw [map_true, Bool.not_true, Bool.not_false, Bool.cond_false, Bool.cond_true, zero_add]

/-- The definition of a bind, as the game writes it for a finite first step: the mass of `do let a ← μ; f a` at
`b` is the sum over the first steps `a` of the mass `μ a` times the mass of `f a` at `b`. -/
theorem bind_apply {α β : Type} [Fintype α] (μ : DiscreteMeasure α) (f : α → DiscreteMeasure β) (b : β) :
    (do let a ← μ; f a) b = ∑ a, μ a * f a b := by
  rw [← MeasureTheory.DiscreteMeasure.bind_eq_bind, MeasureTheory.DiscreteMeasure.bind_apply, tsum_fintype]

/-- The mass of a bind at `true`: through `true` and through `false` (Building with coins). -/
theorem bind_true (μ : DiscreteMeasure Bool) (f : Bool → DiscreteMeasure Bool) :
    (do let x ← μ; f x) true = μ true * f true true + μ false * f false true := by
  rw [← MeasureTheory.DiscreteMeasure.bind_eq_bind, MeasureTheory.DiscreteMeasure.bind_apply, tsum_fintype, Fintype.sum_bool]

/-- A coin whose result is not used changes nothing. -/
theorem coin_unused {β : Type} (p : I) (ν : DiscreteMeasure β) : (do let _ ← coin p; ν) = ν :=
  MeasureTheory.DiscreteMeasure.bind_const_of_hasSum (MeasureTheory.DiscreteMeasure.hasSum_coin p) ν

/-- Two numbers behind one test are one number behind it (Bool, proved there on `ℕ`; for masses too). -/
theorem cond_add_cond {α : Type} [AddZeroClass α] (c : Bool) (x y : α) :
    (bif c then x else 0) + (bif c then y else 0) = bif c then x + y else 0 := by
  cases c
  · simp only [Bool.cond_false, add_zero]
  · rfl

/-- A move that does nothing: the distribution stays. -/
theorem map_id {α : Type} (μ : DiscreteMeasure α) : μ.map (fun x => x) = μ :=
  MeasureTheory.DiscreteMeasure.id_map μ

/-- Two moves are one move. -/
theorem map_map {α β γ : Type} (μ : DiscreteMeasure α) (f : α → β) (g : β → γ) :
    (μ.map f).map g = μ.map (fun x => g (f x)) := (comp_map f g μ).symm

/-- A move on a point mass moves the point. -/
theorem map_pure {α β : Type} (a : α) (f : α → β) : (pure a : DiscreteMeasure α).map f = pure (f a) :=
  LawfulApplicative.map_pure f a

/-- A move after a draw goes into it. -/
theorem map_bind {α β γ : Type} (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) (f : β → γ) :
    (do let x ← μ; g x).map f = (do let x ← μ; (g x).map f) := _root_.map_bind f μ g

/-- A move on a draw goes into what follows. -/
theorem bind_map_left {α β γ : Type} (μ : DiscreteMeasure α) (f : α → β) (g : β → DiscreteMeasure γ) :
    (do let x ← μ.map f; g x) = (do let x ← μ; g (f x)) := _root_.bind_map_left f μ g

/-- A move is a draw and then a point mass. -/
theorem map_eq_pure_bind {α β : Type} (μ : DiscreteMeasure α) (f : α → β) :
    μ.map f = (do let x ← μ; pure (f x)) := _root_.map_eq_pure_bind f μ

/-- Independence: two coins, both `true`, is a coin `p * q`. -/
theorem coin_and (p q : I) : (do let x ← coin p; let y ← coin q; pure (x && y)) = coin (p * q) := by
  rw [← MeasureTheory.DiscreteMeasure.twoCoins_and_eq_coin]
  simp only [_root_.map_eq_pure_bind, seq_eq_bind_map, bind_assoc, pure_bind]

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

/-- One Coin, *Where does the mass go?*: flipped, the coin has the mass `1 - p` at `true`. -/
theorem coin_not_true (p : I) : ((coin p).map not) true = σ p := by
  rw [map_true]
  rw [Bool.not_true, Bool.not_false]
  rw [Bool.cond_false, Bool.cond_true, zero_add]
  rw [coin_false]

/-- One Coin, *Always true*: a constant move sends all the mass to one point. -/
theorem coin_const (p : I) (b : Bool) : (coin p).map (fun _ => b) = pure b := by
  apply bool_ext
  rw [map_true, pure_true]
  cases b
  rw [Bool.cond_false, Bool.cond_false, Bool.cond_false, zero_add]
  rw [Bool.cond_true, Bool.cond_true, Bool.cond_true, coin_total]

/-- One Coin, *Every distribution is a coin*: with the mass `p` at `true`, it is the coin `p` (as
Mathlib's `eq_bernoulliMeasure`: the parameter given, not computed from `μ`). -/
theorem eq_coin (μ : DiscreteMeasure Bool) [Prob μ] (p : I) (h : μ true = p) : μ = coin p := by
  apply bool_ext
  rw [coin_true, h]

/-- World 1, the boss: flipping a coin swaps the masses `p` and `1 - p`. -/
theorem coin_not (p : I) : (coin p).map not = coin (σ p) := by
  apply bool_ext
  rw [coin_not_true, coin_true]

/-- `B(1, p)` is a coin as a number. -/
theorem binom_one (p : I) : (coin p).map Bool.toNat = binom p 1 := by
  rw [binom_succ, binom_zero]
  simp only [pure_bind, add_zero]
  rw [map_eq_pure_bind]

/-- Building with Coins, *A new building block*: one throw more, at the end. -/
theorem binom_succ' (p : I) (n : ℕ) :
    (do let X ← binom p n; let Y ← coin p; pure (X + Y.toNat)) = binom p (n + 1) := by
  induction' n with n ih
  · rw [binom_zero, binom_succ, binom_zero]
    simp only [pure_bind, zero_add, add_zero]
  · rw [binom_succ p n, binom_succ p (n + 1), ← ih]
    simp only [bind_assoc, pure_bind, add_assoc]

/-- Building with Coins, *B(2, p) * B(2, p) = B(4, p)*: the sum of independent binomials. -/
theorem binom_add (p : I) (n m : ℕ) :
    (do let X ← binom p n; let Y ← binom p m; pure (X + Y)) = binom p (n + m) := by
  induction' m with m ih
  · rw [binom_zero]
    simp only [pure_bind, add_zero, bind_pure]
  · rw [← binom_succ' p m, ← add_assoc, ← binom_succ' p (n + m), ← ih]
    simp only [bind_assoc, pure_bind, add_assoc]

/-! Thinning, Binomial, Geometric (2026-11-15). -/

/-- A product of numbers in `[0, 1]`, as a mass. -/
theorem mass_mul (p q : I) : ((p * q : I) : ENNReal) = (p : ENNReal) * (q : ENNReal) := by
  show ENNReal.ofReal ((p : ℝ) * q) = ENNReal.ofReal p * ENNReal.ofReal q
  exact ENNReal.ofReal_mul p.2.1

/-- The mass of a draw that starts with a coin, at any point: through `true` and through `false`. -/
theorem coin_bind_apply {β : Type} (p : I) (f : Bool → DiscreteMeasure β) (x : β) :
    (do let b ← coin p; f b) x = ↑p * f true x + ↑(σ p) * f false x := by
  rw [← MeasureTheory.DiscreteMeasure.bind_eq_bind, MeasureTheory.DiscreteMeasure.bind_apply,
    tsum_fintype, Fintype.sum_bool, coin_true, coin_false]

/-- A point mass at its point. -/
theorem pure_self {α : Type} [DecidableEq α] (a : α) : (pure a : DiscreteMeasure α) a = 1 :=
  MeasureTheory.DiscreteMeasure.pure_apply_self

/-- The point mass at `0`, elsewhere. -/
theorem pure_zero_succ (k : ℕ) : (pure 0 : DiscreteMeasure ℕ) (k + 1) = 0 :=
  MeasureTheory.DiscreteMeasure.pure_apply_nonself (Nat.succ_ne_zero k)

/-- One more: the mass at `k + 1` is the old mass at `k`. -/
theorem shift_succ (μ : DiscreteMeasure ℕ) (k : ℕ) : (do let Y ← μ; pure (1 + Y)) (k + 1) = μ k := by
  rw [← MeasureTheory.DiscreteMeasure.bind_eq_bind, MeasureTheory.DiscreteMeasure.bind_apply,
    tsum_eq_single k]
  · rw [add_comm 1 k]; erw [MeasureTheory.DiscreteMeasure.pure_apply_self, mul_one]
  · intro b hb
    erw [MeasureTheory.DiscreteMeasure.pure_apply_nonself (by omega), mul_zero]

/-- One more is never `0`. -/
theorem shift_zero (μ : DiscreteMeasure ℕ) : (do let Y ← μ; pure (1 + Y)) 0 = 0 := by
  rw [← MeasureTheory.DiscreteMeasure.bind_eq_bind, MeasureTheory.DiscreteMeasure.bind_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro b
  erw [MeasureTheory.DiscreteMeasure.pure_apply_nonself (by omega), mul_zero]

/-- Thinning, *Keeping with probability q*: a coin `p`, and on `true` a coin `q`. -/
theorem coin_thin (p q : I) : (do let x ← coin p; bif x then coin q else pure false) = coin (p * q) := by
  apply bool_ext
  rw [bind_true, Bool.cond_true, Bool.cond_false, pure_true, Bool.cond_false, mul_zero, add_zero,
    coin_true, coin_true, coin_true, mass_mul]

/-- Binomial: a coin `p`, then as many coins `q` as it shows. -/
theorem coin_bind_binom (p q : I) :
    (do let C ← coin p; binom q C.toNat) = (do let B ← coin (p * q); pure B.toNat) := by
  rw [← coin_thin]
  simp only [bind_assoc]
  congr 1
  funext x
  cases x
  rw [Bool.toNat_false, binom_zero, Bool.cond_false, pure_bind, Bool.toNat_false]
  rw [Bool.toNat_true, Bool.cond_true, binom_succ, binom_zero]
  simp only [pure_bind, add_zero]

/-- The same, with something after it. -/
theorem coin_bind_binom' {β : Type} (p q : I) (f : ℕ → DiscreteMeasure β) :
    (do let C ← coin p; let U ← binom q C.toNat; f U) = (do let B ← coin (p * q); f B.toNat) := by
  rw [← bind_assoc, coin_bind_binom, bind_assoc]
  simp only [pure_bind]

theorem binom_succ_zero (p : I) (n : ℕ) : binom p (n + 1) 0 = ↑(σ p) * binom p n 0 := by
  rw [binom_succ, coin_bind_apply]
  simp only [Bool.toNat_true, Bool.toNat_false, zero_add, bind_pure]
  rw [shift_zero, mul_zero, zero_add]

theorem binom_succ_succ (p : I) (n k : ℕ) :
    binom p (n + 1) (k + 1) = ↑p * binom p n k + ↑(σ p) * binom p n (k + 1) := by
  rw [binom_succ, coin_bind_apply]
  simp only [Bool.toNat_true, Bool.toNat_false, zero_add, bind_pure]
  rw [shift_succ]

theorem binom_all_false (p : I) (n : ℕ) : binom p n 0 = ↑(σ p) ^ n := by
  induction' n with n ih
  rw [binom_zero, pure_self, pow_zero]
  rw [binom_succ_zero, ih, pow_succ, mul_comm]

theorem binom_above (p : I) (n k : ℕ) : binom p n (n + k + 1) = 0 := by
  induction' n with n ih generalizing k
  rw [zero_add, binom_zero, pure_zero_succ]
  rw [binom_succ_succ, add_right_comm n 1 k, ih, add_assoc n k 1, ih, mul_zero, mul_zero, add_zero]

theorem binom_diag (p : I) (n : ℕ) : binom p n n = ↑p ^ n := by
  induction' n with n ih
  rw [binom_zero, pure_self, pow_zero]
  rw [binom_succ_succ, ih, binom_above p n 0, mul_zero, add_zero, pow_succ, mul_comm]

/-- Binomial, the boss: `k` times `true` and `m` times `false`. -/
theorem binom_formula (p : I) (k m : ℕ) :
    binom p (k + m) k = ↑p ^ k * ↑(σ p) ^ m * ((k + m).choose k : ENNReal) := by
  induction' m with m ih generalizing k
  rw [add_zero, binom_diag, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, mul_one]
  induction' k with k ih2
  rw [zero_add, binom_all_false, pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one]
  rw [← add_assoc, binom_succ_succ, ih (k + 1), add_right_comm k 1 m, add_assoc k m 1, ih2,
    Nat.choose_succ_succ', Nat.cast_add]
  ring

/-- Binomial, thinning: of `binom p n` successes each is kept with probability `q`. -/
theorem binom_thin (p q : I) (n : ℕ) : (do let X ← binom p n; binom q X) = binom (p * q) n := by
  induction' n with n ih
  rw [binom_zero, binom_zero, pure_bind, binom_zero]
  rw [binom_succ, binom_succ (p * q), ← ih]
  simp only [bind_assoc, pure_bind]
  simp only [← binom_add]
  simp only [bind_comm (binom p n) (binom q _)]
  rw [coin_bind_binom']

/-- The geometric distribution, by its masses: `p` at `0`, and one step further always `1 - p`
times as much (the number of `false` before the first `true`). -/
noncomputable def geomMass (p : I) : ℕ → ENNReal
  | 0 => ↑p
  | k + 1 => ↑(σ p) * geomMass p k

noncomputable def geom (p : I) : DiscreteMeasure ℕ := ⟨geomMass p⟩

theorem geom_zero (p : I) : geom p 0 = ↑p := rfl

theorem geom_succ (p : I) (k : ℕ) : geom p (k + 1) = ↑(σ p) * geom p k := rfl

theorem geom_formula (p : I) (k : ℕ) : geom p k = ↑(σ p) ^ k * ↑p := by
  induction' k with k ih
  rw [geom_zero, pow_zero, one_mul]
  rw [geom_succ, ih, ← mul_assoc, ← pow_succ']

theorem geom_memoryless (p : I) (k m : ℕ) : geom p (k + m) = ↑(σ p) ^ k * geom p m := by
  induction' k with k ih
  rw [zero_add, pow_zero, one_mul]
  rw [add_right_comm, geom_succ, ih, ← mul_assoc, ← pow_succ']

theorem geom_first (p : I) :
    geom p = (do let x ← coin p; bif x then pure 0 else (do let Y ← geom p; pure (1 + Y))) := by
  ext k
  cases k
  rw [coin_bind_apply, Bool.cond_true, Bool.cond_false, pure_self, shift_zero, mul_zero, add_zero,
    mul_one, geom_zero]
  rw [coin_bind_apply, Bool.cond_true, Bool.cond_false, pure_zero_succ, shift_succ, mul_zero,
    zero_add, geom_succ]

/-! Sequences (2026-11-15): `iidSequence n μ` draws `n` times from `μ`, independently, as a list. -/

theorem seq_zero {α : Type} (μ : DiscreteMeasure α) : iidSequence 0 μ = pure [] :=
  MeasureTheory.DiscreteMeasure.iidSequence_zero μ

theorem seq_succ {α : Type} (μ : DiscreteMeasure α) (n : ℕ) :
    iidSequence (n + 1) μ = (do let y ← μ; let l ← iidSequence n μ; pure (y :: l)) :=
  (MeasureTheory.DiscreteMeasure.iidSequence_cons μ).symm

theorem seq_succ_apply {α : Type} [DecidableEq α] (μ : DiscreteMeasure α) (n : ℕ) (a : α) (l : List α) :
    iidSequence (n + 1) μ (a :: l) = μ a * iidSequence n μ l := by
  rw [MeasureTheory.DiscreteMeasure.iidSequence, List.replicate_succ,
    MeasureTheory.DiscreteMeasure.sequence_cons_apply_cons]
  rfl

theorem seq_zero_nil {α : Type} (μ : DiscreteMeasure α) : iidSequence 0 μ [] = 1 := by
  rw [seq_zero]; exact MeasureTheory.DiscreteMeasure.pure_apply_self

theorem count_true_cons (y : Bool) (l : List Bool) : (y :: l).count true = y.toNat + l.count true := by
  cases y <;> simp [add_comm]

/-- Sequences, the boss: `binom p n` counts the `true` in `n` independent coins. -/
theorem binom_eq_count (p : I) (n : ℕ) :
    binom p n = (iidSequence n (coin p)).map (fun l => l.count true) := by
  induction' n with n ih
  rw [seq_zero, map_pure, binom_zero]
  rfl
  rw [binom_succ, seq_succ, ih]
  simp only [map_bind, map_pure, bind_map_left, count_true_cons]

/-! Binomial symmetry, geometric total mass (2026-11-15). -/

theorem symm_twice (p : I) : σ (σ p) = p := unitInterval.symm_symm p

/-- Binomial, encore: `true` and `false` swapped. -/
theorem binom_symm (p : I) (k m : ℕ) : binom (σ p) (k + m) m = binom p (k + m) k := by
  rw [add_comm k m, binom_formula, add_comm m k, binom_formula, symm_twice, Nat.choose_symm_add]
  ring

/-- `1 - (1 - p) = p`, as masses. -/
theorem one_sub_symm (p : I) : 1 - (↑(σ p) : ENNReal) = ↑p := by
  rw [← add_symm_eq_one p, ENNReal.add_sub_cancel_right]
  exact ENNReal.ofReal_ne_top

/-- A number `p ≠ 0` is a mass `≠ 0`. -/
theorem mass_ne_zero {p : I} (h : p ≠ 0) : (↑p : ENNReal) ≠ 0 := by
  show ENNReal.ofReal p ≠ 0
  rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact lt_of_le_of_ne p.2.1 (fun e => h (Subtype.ext e.symm))

/-- A number in `[0, 1]` is a finite mass. -/
theorem mass_finite (p : I) : (↑p : ENNReal) ≠ ⊤ := ENNReal.ofReal_ne_top

/-- The mass of `1` is `1` (a rule of the game, in *One Coin*). -/
theorem mass_one : ((1 : I) : ENNReal) = 1 := by
  show ENNReal.ofReal 1 = 1
  simp

/-- The mass of `0` is `0`. -/
theorem mass_zero : ((0 : I) : ENNReal) = 0 := by
  show ENNReal.ofReal 0 = 0
  simp

/-- `a + p = 1` says that `a` is the mass `σ p`. -/
theorem eq_symm_of_add (a : ENNReal) (p : I) (h : a + ↑p = 1) : a = ↑(σ p) := by
  rw [← add_symm_eq_one p, add_comm (↑p : ENNReal)] at h
  exact (ENNReal.add_left_inj (mass_finite p)).mp h

/-- Geometric: the total mass is one (when `p ≠ 0`). -/
theorem geom_total (p : I) (h : p ≠ 0) : ∑' k, geom p k = 1 := by
  simp only [geom_formula]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, one_sub_symm,
    ENNReal.inv_mul_cancel (mass_ne_zero h) (mass_finite p)]

/-! Hypergeometric, drawn ball by ball (2026-11-15). -/

/-- The chance to draw a white ball from an urn with `w` white and `b` black balls (`0` for an empty urn). -/
noncomputable def frac (w b : ℕ) : I :=
  ⟨(w : ℝ) / (w + b), div_nonneg (Nat.cast_nonneg _) (by positivity),
    div_le_one_of_le₀ (by linarith [(Nat.cast_nonneg b : (0:ℝ) ≤ b)]) (by positivity)⟩

/-- The hypergeometric distribution, drawn ball by ball: the number of white balls in `n` draws
without replacement from an urn with `w` white and `b` black balls. -/
noncomputable def hyper : ℕ → ℕ → ℕ → DiscreteMeasure ℕ
  | _, _, 0 => pure 0
  | w, b, n + 1 => do
      let X ← coin (frac w b)
      bif X then (do let Y ← hyper (w - 1) b n; pure (1 + Y)) else hyper w (b - 1) n

theorem hyper_zero (w b : ℕ) : hyper w b 0 = pure 0 := rfl

theorem hyper_succ (w b n : ℕ) : hyper w b (n + 1) = (do
    let X ← coin (frac w b)
    bif X then (do let Y ← hyper (w - 1) b n; pure (1 + Y)) else hyper w (b - 1) n) := rfl

theorem frac_zero (b : ℕ) : frac 0 b = 0 := by
  apply Subtype.ext; simp [frac]

theorem frac_white (w : ℕ) : frac (w + 1) 0 = 1 := by
  apply Subtype.ext
  show ((↑(w + 1) : ℝ) / (↑(w + 1) + ↑(0 : ℕ))) = 1
  rw [Nat.cast_zero, add_zero]
  exact div_self (by positivity)

theorem coin_zero : coin 0 = pure false := by
  apply bool_ext; rw [coin_true, pure_true, Bool.cond_false]
  show ENNReal.ofReal 0 = 0
  simp

theorem coin_one : coin 1 = pure true := by
  apply bool_ext; rw [coin_true, pure_true, Bool.cond_true]
  show ENNReal.ofReal 1 = 1
  simp

theorem cond_same {α : Type} (c : Bool) (a : α) : (bif c then a else a) = a := by cases c <;> rfl

theorem hyper_black (b n : ℕ) : hyper 0 b n = pure 0 := by
  induction' n with n ih generalizing b
  rw [hyper_zero]
  rw [hyper_succ, frac_zero, coin_zero, pure_bind, Bool.cond_false, ih]

theorem hyper_white (w : ℕ) : hyper w 0 w = pure w := by
  induction' w with w ih
  rw [hyper_zero]
  rw [hyper_succ, frac_white, coin_one, pure_bind, Bool.cond_true, Nat.add_sub_cancel, ih, pure_bind,
    add_comm]

/-- Hypergeometric, the boss: drawing all the balls, one has all the white ones. -/
theorem hyper_all (w b : ℕ) : hyper w b (w + b) = pure w := by
  induction' w with w ih generalizing b
  rw [zero_add, hyper_black]
  induction' b with b ih2
  rw [add_zero, hyper_white]
  rw [← add_assoc, hyper_succ, Nat.add_sub_cancel, Nat.add_sub_cancel, ih2, add_right_comm, add_assoc,
    ih, pure_bind, add_comm 1 w]
  simp only [cond_same]
  rw [coin_unused]

/-! Markov chains on `Bool` (Coins that Wait, 2026-11-15). -/

/-- The mass of a bind at `false`: through `true` and through `false`. -/
theorem bind_false (μ : DiscreteMeasure Bool) (f : Bool → DiscreteMeasure Bool) :
    (do let x ← μ; f x) false = μ true * f true false + μ false * f false false := by
  rw [← MeasureTheory.DiscreteMeasure.bind_eq_bind, MeasureTheory.DiscreteMeasure.bind_apply,
    tsum_fintype, Fintype.sum_bool]

/-- A draw whose outcome is not used changes nothing. -/
theorem prob_unused {β : Type} (μ : DiscreteMeasure Bool) [h : Prob μ] (ν : DiscreteMeasure β) :
    (do let _ ← μ; ν) = ν :=
  MeasureTheory.DiscreteMeasure.bind_const_of_hasSum h.hasSum ν

/-! Real numbers: from masses to `ℝ` (2026-11-15). -/

theorem mass_eq_ofReal (p : I) : (↑p : ENNReal) = ENNReal.ofReal (p : ℝ) := rfl

theorem mass_mul_real (p q : I) : (↑p : ENNReal) * ↑q = ENNReal.ofReal ((p : ℝ) * q) :=
  (ENNReal.ofReal_mul p.2.1).symm

theorem real_mul_nonneg (p q : I) : 0 ≤ (p : ℝ) * q := mul_nonneg p.2.1 q.2.1

theorem symm_real (p : I) : ((σ p : I) : ℝ) = 1 - p := unitInterval.coe_symm_eq p

/-- Balance: a number of `I` is `≥ 0` (as a real number). -/
theorem real_nonneg (p : I) : 0 ≤ (p : ℝ) := p.2.1

/-- Balance, *1 − p, really*: `p + (1 - p) = 1` in `ℝ`. -/
theorem add_symm_real (p : I) : (p : ℝ) + (σ p : I) = 1 := by
  rw [symm_real]; ring

/-- Balance, *Computing with a hypothesis*: in balance, the mass at `true` stays (in `ℝ`). -/
theorem balance {p q r : ℝ} (h : (1 - p) * r = p * (1 - q)) : p * q + (1 - p) * r = p := by
  linear_combination h

/-- Real numbers, the boss: a coin that stays, from the balance of what flows. -/
theorem coin_stays (p q r : I) (h : (1 - (p : ℝ)) * r = p * (1 - q)) :
    (do let x ← coin p; bif x then coin q else coin r) = coin p := by
  apply bool_ext
  rw [bind_true, Bool.cond_true, Bool.cond_false]
  rw [coin_true, coin_true, coin_true, coin_false]
  rw [mass_mul_real, mass_mul_real, ← ENNReal.ofReal_add (real_mul_nonneg p q) (real_mul_nonneg (σ p) r),
    symm_real, mass_eq_ofReal]
  congr 1
  linear_combination h

/-! Rules of 2026-11-22: a first induction, the mass of a list, one draw from the urn. -/

/-- Counting: a coin that never shows `true` is never counted. -/
theorem binom_never (n : ℕ) : binom 0 n = pure 0 := by
  induction' n with n ih
  rw [binom_zero]
  rw [binom_succ, coin_zero, pure_bind, ih, pure_bind]
  rfl

theorem count_false_cons (y : Bool) (l : List Bool) : (y :: l).count false = (!y).toNat + l.count false := by
  cases y <;> simp [add_comm]

/-- Sequences: one more entry in front, one more factor. -/
theorem mass_cons (p : I) (y : Bool) (l : List Bool) :
    coin p y * ((↑p : ENNReal) ^ l.count true * (↑(σ p) : ENNReal) ^ l.count false) =
      (↑p : ENNReal) ^ (y :: l).count true * (↑(σ p) : ENNReal) ^ (y :: l).count false := by
  rw [count_true_cons, count_false_cons]
  cases y
  rw [coin_false, Bool.toNat_false, Bool.not_false, Bool.toNat_true]
  ring
  rw [coin_true, Bool.toNat_true, Bool.not_true, Bool.toNat_false]
  ring

/-- Sequences: the mass of a list depends only on its numbers of `true` and `false`. -/
theorem seq_mass (p : I) (l : List Bool) :
    iidSequence l.length (coin p) l = (↑p : ENNReal) ^ l.count true * (↑(σ p) : ENNReal) ^ l.count false := by
  induction' l with y l ih
  rw [List.length_nil, seq_zero_nil, List.count_nil, List.count_nil]
  ring
  rw [List.length_cons, seq_succ_apply, ih, mass_cons]

theorem frac_real (w b : ℕ) : ((frac w b : I) : ℝ) = (w : ℝ) / ((w : ℝ) + b) := rfl

theorem pure_one_zero : (pure 1 : DiscreteMeasure ℕ) 0 = 0 :=
  MeasureTheory.DiscreteMeasure.pure_apply_nonself Nat.zero_ne_one

theorem hyper_one_one (w b : ℕ) : hyper w b 1 1 = ↑(frac w b) := by
  rw [hyper_succ, coin_bind_apply, Bool.cond_true, Bool.cond_false, shift_succ, hyper_zero, hyper_zero,
    pure_self, pure_zero_succ, mul_one, mul_zero, add_zero]

theorem hyper_one_zero (w b : ℕ) : hyper w b 1 0 = ↑(σ (frac w b)) := by
  rw [hyper_succ, coin_bind_apply, Bool.cond_true, Bool.cond_false, shift_zero, hyper_zero, pure_self,
    mul_zero, zero_add, mul_one]

/-- Hypergeometric, the boss: the second ball is white as often as the first. -/
theorem second_ball (w b : ℕ) :
    (do let X ← coin (frac (w + 1) (b + 1)); bif X then coin (frac w (b + 1)) else coin (frac (w + 1) b)) =
      coin (frac (w + 1) (b + 1)) := by
  apply coin_stays
  rw [frac_real, frac_real, frac_real]
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp
  ring

end ProbGame

open ProbGame

-- (the game's simp is simp only with a fixed list of rules: some of them are unused in a goal)
set_option linter.unusedSimpArgs false
