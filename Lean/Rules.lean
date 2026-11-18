/-!
# The rules of the proof game

The context in which the levels are proved (base: Mathlib's `PMF`, the probability mass functions;
the bridge loads `import Journal.Notes.DiscreteMeasure.Thinning`, which contains it). The player sees
`coin p`, `binom p n`, `pure`, `do` blocks and `f <$> μ`: `PMF` is a monad in Mathlib, with the laws
of Lean's core (`pure_bind`, `bind_pure`, `bind_assoc`, `map_pure`, `bind_map_left`, `map_bind`).
Mathlib's own `PMF.bernoulli` and `PMF.binomial` are deprecated (for measures); the coin and the
binomial distribution are defined here.

Rules that are given (the axioms of the game, as Peano's in the Natural Number Game) and lemmas
the player proves in a level are both here; the game unlocks the lemmas one after another.
-/

open unitInterval

namespace ProbGame

/-! World 1: what a distribution on `Bool` is, and where the mass of a move goes. -/

/-- A number of `I` as a mass, written `↑p`. -/
@[coe] noncomputable def mass (p : I) : ENNReal := ENNReal.ofReal p
noncomputable instance : CoeTC I ENNReal := ⟨mass⟩

/-- The two masses of a coin add up to one. -/
theorem coin_sum (p : I) : ∑ b, (bif b then (p : ENNReal) else ↑(σ p)) = 1 := by
  rw [Fintype.sum_bool, Bool.cond_true, Bool.cond_false]
  show ENNReal.ofReal p + ENNReal.ofReal (σ p : ℝ) = 1
  rw [← ENNReal.ofReal_add p.2.1 (σ p).2.1, unitInterval.coe_symm_eq, add_sub_cancel, ENNReal.ofReal_one]

/-- The coin with probability `p`: mass `p` at `true` and `1 - p` at `false`. -/
noncomputable def coin (p : I) : PMF Bool :=
  PMF.ofFintype (fun b => bif b then (p : ENNReal) else ↑(σ p)) (coin_sum p)

/-- The mass of a coin at `true`. -/
theorem coin_true (p : I) : coin p true = p := rfl

/-- The mass of a coin at `false`. -/
theorem coin_false (p : I) : coin p false = σ p := rfl

/-- The total mass of a coin is one. -/
theorem coin_total (p : I) : coin p true + coin p false = 1 := by
  have := coin_sum p
  rw [Fintype.sum_bool] at this; exact this

/-- The definition of a point mass, as the game writes it: mass one at its point, zero elsewhere. -/
theorem pure_apply {α : Type} [DecidableEq α] (a b : α) :
    (pure a : PMF α) b = bif a == b then 1 else 0 := by
  show PMF.pure a b = _
  rw [PMF.pure_apply]
  by_cases h : a = b
  · subst h; simp
  · simp [h, Ne.symm h]

/-- The mass of a point mass at `true`: one if it sits there, else zero. -/
theorem pure_true (b : Bool) : (pure b : PMF Bool) true = bif b then 1 else 0 := by
  rw [pure_apply]; cases b <;> rfl

/-- The total mass of a distribution on `Bool` is one. -/
theorem mass_total (μ : PMF Bool) : μ true + μ false = 1 := by
  rw [← PMF.tsum_coe μ, tsum_fintype, Fintype.sum_bool]

/-- A mass of a distribution on `Bool` is at most one. -/
theorem mass_le_one (μ : PMF Bool) (b : Bool) : μ b ≤ 1 := by
  rw [← mass_total μ]
  cases b
  · exact le_add_self
  · exact le_self_add

/-- A mass of a distribution is finite (at most one). -/
theorem mass_ne_top {μ : PMF Bool} {b : Bool} : μ b ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (mass_le_one μ b)

/-- One Coin, *The rest of the mass*: what is not at `b` lies at `!b`. -/
theorem mass_not (μ : PMF Bool) (b : Bool) : μ b = 1 - μ (!b) := by
  cases b
  · rw [Bool.not_false, ← mass_total μ, ENNReal.add_sub_cancel_left mass_ne_top]
  · rw [Bool.not_true, ← mass_total μ, add_comm, ENNReal.add_sub_cancel_left mass_ne_top]

/-- One Coin, *One bar is enough*: two distributions on `Bool` are the same when they have the
same mass at `true`. -/
theorem bool_ext (μ ν : PMF Bool) (h : μ true = ν true) : μ = ν := by
  ext x
  cases x
  · rw [mass_not μ false, mass_not ν false, Bool.not_false, h]
  · exact h

-- The masses of coins and point masses are computing, not rules of the game: `norm_num` (in the
-- inventory from *Building with Coins* on) knows them.
attribute [simp] coin_true coin_false pure_true

/-- $`p + (1 - p) = 1`, as masses: computing for `norm_num`. -/
@[simp] theorem add_symm_eq_one (p : I) : (↑p : ENNReal) + ↑(σ p) = 1 := by
  rw [← coin_true, ← coin_false, coin_total]

/-- The mass at `true`, as a number in `[0, 1]` (for `coin`). -/
noncomputable def chance (μ : PMF Bool) : I :=
  ⟨(μ true).toReal, ENNReal.toReal_nonneg, by
    have h : μ true ≤ 1 := (mass_total μ) ▸ le_self_add
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top h⟩

/-- `chance μ`, as a mass, is the mass at `true`. -/
theorem chance_eq (μ : PMF Bool) : (chance μ : ENNReal) = μ true := by
  show ENNReal.ofReal (μ true).toReal = μ true
  exact ENNReal.ofReal_toReal mass_ne_top

/-- The definition of a move, as the game writes it: the mass of `f <$> μ` at `b` is the sum of the
masses `μ a` over the points `a` with `f a = b` (a finite sum: finitely many points). -/
theorem map_apply {α : Type} [Fintype α] (f : α → Bool) (μ : PMF α) (b : Bool) :
    (f <$> μ) b = ∑ a, (bif f a == b then μ a else 0) := by
  rw [PMF.monad_map_eq_map, PMF.map_apply, tsum_fintype]
  congr 1; funext a
  cases h : f a <;> cases b <;> simp

/-- Where the mass of a move goes: the mass of `f <$> μ` at `true` is the mass of `μ` at the points
that `f` sends to `true` (`bif c then a else b` is `a` when `c` is `true`, else `b`). -/
theorem map_true (f : Bool → Bool) (μ : PMF Bool) :
    (f <$> μ) true = (bif f true then μ true else 0) + (bif f false then μ false else 0) := by
  rw [map_apply, Fintype.sum_bool]
  cases f true <;> cases f false <;> rfl

/-- The definition of a bind, as the game writes it for a finite first step: the mass of `μ >>= f` at
`b` is the sum over the first steps `a` of the mass `μ a` times the mass of `f a` at `b`. -/
theorem bind_apply {α β : Type} [Fintype α] (μ : PMF α) (f : α → PMF β) (b : β) :
    (do let a ← μ; f a) b = ∑ a, μ a * f a b := by
  show (μ.bind f) b = _
  rw [PMF.bind_apply, tsum_fintype]

/-- The mass of a bind at `true`: through `true` and through `false` (Building with coins). -/
theorem bind_true (μ : PMF Bool) (f : Bool → PMF Bool) :
    (do let x ← μ; f x) true = μ true * f true true + μ false * f false true := by
  rw [bind_apply, Fintype.sum_bool]

/-- A coin whose result is not used changes nothing. -/
theorem coin_unused {β : Type} (p : I) (ν : PMF β) : (do let _ ← coin p; ν) = ν :=
  PMF.bind_const (coin p) ν

/-- Two moves are one move. -/
theorem map_map {α β γ : Type} (μ : PMF α) (f : α → β) (g : β → γ) :
    g <$> (f <$> μ) = (fun x => g (f x)) <$> μ := (comp_map f g μ).symm

/-- Independence: two coins, both `true`, is a coin `p * q`. -/
theorem coin_and (p q : I) : (do let x ← coin p; let y ← coin q; pure (x && y)) = coin (p * q) := by
  apply bool_ext
  rw [bind_true, bind_true, bind_true, pure_true, pure_true, pure_true, pure_true]
  simp only [Bool.and_true, Bool.and_false, Bool.cond_true, Bool.cond_false, mul_one, mul_zero, add_zero]
  rw [coin_true, coin_true, coin_true]
  show ENNReal.ofReal p * ENNReal.ofReal q = ENNReal.ofReal ((p : ℝ) * q)
  rw [ENNReal.ofReal_mul p.2.1]

/-- Independence: the order of two independent draws does not matter. -/
theorem bind_comm {α β γ : Type} (μ : PMF α) (ν : PMF β) (f : α → β → PMF γ) :
    (do let x ← μ; let y ← ν; f x y) = (do let y ← ν; let x ← μ; f x y) :=
  PMF.bind_comm μ ν f

/-- De Morgan. -/
theorem or_eq (x y : Bool) : (x || y) = !(!x && !y) := by cases x <;> cases y <;> rfl

/-- The binomial distribution: the number of `true` in `n` coins `p`, one after the other. -/
noncomputable def binom (p : I) : ℕ → PMF ℕ
  | 0 => pure 0
  | n + 1 => do let X ← coin p; let Y ← binom p n; pure (X.toNat + Y)

/-- The binomial distribution, by its definition: no throw. -/
theorem binom_zero (p : I) : binom p 0 = pure 0 := rfl

/-- The binomial distribution, by its definition: one throw more. -/
theorem binom_succ (p : I) (n : ℕ) :
    binom p (n + 1) = (do let X ← coin p; let Y ← binom p n; pure (X.toNat + Y)) := rfl

/-! The lemmas the player proves; the game unlocks each after its level. -/

/-- One Coin, *Where does the mass go?*: flipped, the coin has the mass `1 - p` at `true`. -/
theorem coin_not_true (p : I) : (not <$> coin p) true = σ p := by
  rw [map_true]
  rw [Bool.not_true, Bool.not_false]
  rw [Bool.cond_false, Bool.cond_true, zero_add]
  rw [coin_false]

/-- One Coin, *Always true*: a constant move sends all the mass to one point. -/
theorem coin_const (p : I) (b : Bool) : (fun _ => b) <$> coin p = pure b := by
  apply bool_ext
  rw [map_true, pure_true]
  cases b
  rw [Bool.cond_false, Bool.cond_false, Bool.cond_false, zero_add]
  rw [Bool.cond_true, Bool.cond_true, Bool.cond_true, coin_total]

/-- One Coin, *Every distribution is a coin*. -/
theorem eq_coin (μ : PMF Bool) : μ = coin (chance μ) := by
  apply bool_ext
  rw [coin_true, chance_eq]

/-- World 1, the boss: flipping a coin swaps the masses `p` and `1 - p`. -/
theorem coin_not (p : I) : not <$> coin p = coin (σ p) := by
  apply bool_ext
  rw [coin_not_true, coin_true]

/-- `B(1, p)` is a coin as a number. -/
theorem binom_one (p : I) : Bool.toNat <$> coin p = binom p 1 := by
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
theorem coin_bind_apply {β : Type} (p : I) (f : Bool → PMF β) (x : β) :
    (do let b ← coin p; f b) x = ↑p * f true x + ↑(σ p) * f false x := by
  rw [bind_apply, Fintype.sum_bool, coin_true, coin_false]

/-- A point mass at its point. -/
theorem pure_self {α : Type} [DecidableEq α] (a : α) : (pure a : PMF α) a = 1 :=
  PMF.pure_apply_self a

/-- The point mass at `0`, elsewhere. -/
theorem pure_zero_succ (k : ℕ) : (pure 0 : PMF ℕ) (k + 1) = 0 :=
  PMF.pure_apply_of_ne _ _ (Nat.succ_ne_zero k)

/-- One more: the mass at `k + 1` is the old mass at `k`. -/
theorem shift_succ (μ : PMF ℕ) (k : ℕ) : (do let Y ← μ; pure (1 + Y)) (k + 1) = μ k := by
  show (μ.bind fun Y => PMF.pure (1 + Y)) (k + 1) = μ k
  rw [PMF.bind_apply, tsum_eq_single k]
  · rw [add_comm 1 k, PMF.pure_apply_self, mul_one]
  · intro b hb
    rw [PMF.pure_apply_of_ne _ _ (by omega), mul_zero]

/-- One more is never `0`. -/
theorem shift_zero (μ : PMF ℕ) : (do let Y ← μ; pure (1 + Y)) 0 = 0 := by
  show (μ.bind fun Y => PMF.pure (1 + Y)) 0 = 0
  rw [PMF.bind_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro b
  rw [PMF.pure_apply_of_ne _ _ (by omega), mul_zero]

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
theorem coin_bind_binom' {β : Type} (p q : I) (f : ℕ → PMF β) :
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

theorem geomMass_formula (p : I) (k : ℕ) : geomMass p k = ↑(σ p) ^ k * ↑p := by
  induction' k with k ih
  · rw [geomMass, pow_zero, one_mul]
  · rw [geomMass, ih, ← mul_assoc, ← pow_succ']

/-- Geometric: the masses add up to one (when `p ≠ 0`); so `geom p` is a distribution. -/
theorem geomMass_total (p : I) (h : p ≠ 0) : ∑' k, geomMass p k = 1 := by
  simp only [geomMass_formula]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, one_sub_symm,
    ENNReal.inv_mul_cancel (mass_ne_zero h) (mass_finite p)]

/-- Two numbers `≠ 0` have a product `≠ 0`. -/
instance (p q : I) [hp : Fact (p ≠ 0)] [hq : Fact (q ≠ 0)] : Fact (p * q ≠ 0) :=
  ⟨fun h => by
    have h' : (p : ℝ) * q = 0 := congrArg Subtype.val h
    rcases mul_eq_zero.mp h' with e | e
    · exact hp.out (Subtype.ext e)
    · exact hq.out (Subtype.ext e)⟩

/-- The geometric distribution (for `p ≠ 0`: for `p = 0` the first `true` never comes). -/
noncomputable def geom (p : I) [h : Fact (p ≠ 0)] : PMF ℕ :=
  ⟨geomMass p, ENNReal.summable.hasSum_iff.mpr (geomMass_total p h.out)⟩

variable (p : I) [Fact (p ≠ 0)] in
theorem geom_zero : geom p 0 = ↑p := rfl

variable (p : I) [Fact (p ≠ 0)] in
theorem geom_succ (k : ℕ) : geom p (k + 1) = ↑(σ p) * geom p k := rfl

variable (p : I) [Fact (p ≠ 0)] in
theorem geom_formula (k : ℕ) : geom p k = ↑(σ p) ^ k * ↑p := geomMass_formula p k

/-- Geometric: the total mass is one. -/
theorem geom_total (p : I) [Fact (p ≠ 0)] : ∑' k, geom p k = 1 := PMF.tsum_coe _

theorem geom_memoryless (p : I) [Fact (p ≠ 0)] (k m : ℕ) : geom p (k + m) = ↑(σ p) ^ k * geom p m := by
  induction' k with k ih
  rw [zero_add, pow_zero, one_mul]
  rw [add_right_comm, geom_succ, ih, ← mul_assoc, ← pow_succ']

theorem geom_first (p : I) [Fact (p ≠ 0)] :
    geom p = (do let x ← coin p; bif x then pure 0 else (do let Y ← geom p; pure (1 + Y))) := by
  apply PMF.ext; intro k
  cases k
  rw [coin_bind_apply, Bool.cond_true, Bool.cond_false, pure_self, shift_zero, mul_zero, add_zero,
    mul_one, geom_zero]
  rw [coin_bind_apply, Bool.cond_true, Bool.cond_false, pure_zero_succ, shift_succ, mul_zero,
    zero_add, geom_succ]

/-! Sequences (2026-11-15): `iidSequence n μ` draws `n` times from `μ`, independently, as a list. -/

/-- `n` independent draws from `μ`, as a list. -/
noncomputable def iidSequence {α : Type} : ℕ → PMF α → PMF (List α)
  | 0, _ => pure []
  | n + 1, μ => do let y ← μ; let l ← iidSequence n μ; pure (y :: l)

theorem seq_zero {α : Type} (μ : PMF α) : iidSequence 0 μ = pure [] := rfl

theorem seq_succ {α : Type} (μ : PMF α) (n : ℕ) :
    iidSequence (n + 1) μ = (do let y ← μ; let l ← iidSequence n μ; pure (y :: l)) := rfl

theorem seq_succ_apply {α : Type} [DecidableEq α] (μ : PMF α) (n : ℕ) (a : α) (l : List α) :
    iidSequence (n + 1) μ (a :: l) = μ a * iidSequence n μ l := by
  show (μ.bind fun y => (iidSequence n μ).bind fun l' => PMF.pure (y :: l')) (a :: l) = _
  rw [PMF.bind_apply, tsum_eq_single a]
  · congr 1
    rw [PMF.bind_apply, tsum_eq_single l]
    · rw [PMF.pure_apply_self, mul_one]
    · intro l' hl
      rw [PMF.pure_apply_of_ne _ _ (by simp [Ne.symm hl]), mul_zero]
  · intro y hy
    rw [PMF.bind_apply, ENNReal.tsum_eq_zero.mpr, mul_zero]
    intro l'
    rw [PMF.pure_apply_of_ne _ _ (by simp [Ne.symm hy]), mul_zero]

theorem seq_zero_nil {α : Type} (μ : PMF α) : iidSequence 0 μ [] = 1 := by
  rw [seq_zero]; exact PMF.pure_apply_self _

theorem count_true_cons (y : Bool) (l : List Bool) : (y :: l).count true = y.toNat + l.count true := by
  cases y <;> simp [add_comm]

/-- Sequences, the boss: `binom p n` counts the `true` in `n` independent coins. -/
theorem binom_eq_count (p : I) (n : ℕ) :
    binom p n = (fun l => l.count true) <$> iidSequence n (coin p) := by
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

/-! Hypergeometric, drawn ball by ball (2026-11-15). -/

/-- The chance to draw a white ball from an urn with `w` white and `b` black balls (`0` for an empty urn). -/
noncomputable def frac (w b : ℕ) : I :=
  ⟨(w : ℝ) / (w + b), div_nonneg (Nat.cast_nonneg _) (by positivity),
    div_le_one_of_le₀ (by linarith [(Nat.cast_nonneg b : (0:ℝ) ≤ b)]) (by positivity)⟩

/-- The hypergeometric distribution, drawn ball by ball: the number of white balls in `n` draws
without replacement from an urn with `w` white and `b` black balls. -/
noncomputable def hyper : ℕ → ℕ → ℕ → PMF ℕ
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
theorem bind_false (μ : PMF Bool) (f : Bool → PMF Bool) :
    (do let x ← μ; f x) false = μ true * f true false + μ false * f false false := by
  rw [bind_apply, Fintype.sum_bool]

/-- A draw whose outcome is not used changes nothing. -/
theorem prob_unused {β : Type} (μ : PMF Bool) (ν : PMF β) :
    (do let _ ← μ; ν) = ν :=
  PMF.bind_const μ ν

/-! Real numbers: from masses to `ℝ` (2026-11-15). -/

theorem mass_eq_ofReal (p : I) : (↑p : ENNReal) = ENNReal.ofReal (p : ℝ) := rfl

theorem mass_mul_real (p q : I) : (↑p : ENNReal) * ↑q = ENNReal.ofReal ((p : ℝ) * q) :=
  (ENNReal.ofReal_mul p.2.1).symm

theorem real_mul_nonneg (p q : I) : 0 ≤ (p : ℝ) * q := mul_nonneg p.2.1 q.2.1

theorem symm_real (p : I) : ((σ p : I) : ℝ) = 1 - p := unitInterval.coe_symm_eq p

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

end ProbGame

open ProbGame
