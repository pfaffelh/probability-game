/-!
# Solutions: the proofs of the levels, as a player types them, line by line

Checked with `Lean/Rules.lean` in front (`./check-proofs.sh`); `tests/proofs.py` plays them through
the bridge, as the game does.
-/

-- World 1
example (p : I) (μ : DiscreteMeasure Bool) [hμ : Prob μ] (h : μ true = p) : μ = coin p := by
  apply bool_ext
  rw [h, coin_true]
example (p : I) : (not <$> coin p) true = σ p := by
  rw [map_true]
  rw [Bool.not_true, Bool.not_false]
  rw [Bool.cond_false, Bool.cond_true, zero_add]
  rw [coin_false]
example (p : I) : (fun _ => true) <$> coin p = pure true := by
  rw [coin_const]
example (p : I) : not <$> ((fun _ => true) <$> coin p) = pure false := by
  rw [coin_const]
  rw [map_pure]
  rfl
example (p : I) : Bool.toNat <$> coin p = (fun b => if b then 1 else 0) <$> coin p := by
  congr 1
  funext b
  cases b
  rfl
  rfl
example (p : I) : (fun b => if b then (5 : ℤ) else -2) <$> coin p = (fun n : ℕ => 7 * (n : ℤ) - 2) <$> (Bool.toNat <$> coin p) := by
  rw [map_map]
  congr 1
  funext b
  cases b
  rfl
  rfl
example (p : I) : Bool.toNat <$> ((fun _ => false) <$> coin p) = pure 0 := by
  rw [coin_const, map_pure]
  rfl
example (p : I) : not <$> coin p = coin (σ p) := by
  apply bool_ext
  rw [coin_not_true, coin_true]

-- World 2
example (p : I) : (do let x ← coin p; let y ← coin p; pure (x && y)) = coin (p * p) := by
  rw [coin_and]
example (p : I) : (do let x ← coin p; let y ← coin p; pure (x && !y)) = coin (p * σ p) := by
  rw [← coin_and]
  rw [← coin_not]
  simp only [bind_map_left]
example (p : I) : (do let x ← coin p; let y ← coin p; pure (x || y)) = coin (σ (σ p * σ p)) := by
  rw [← coin_not]
  rw [← coin_and]
  rw [← coin_not]
  simp only [bind_map_left, map_bind, map_pure, or_eq]
example (p : I) : (do let x ← coin p; pure (x && !x)) = pure false := by
  simp only [Bool.and_not_self]
  rw [coin_unused]
example (p : I) : (do let x ← coin p; let y ← coin p; pure ((x || y) && !(x && y))) = (do let x ← coin p; let y ← coin p; pure (xor x y)) := by
  congr 1
  funext x
  congr 1
  funext y
  cases x <;> cases y <;> rfl
example (p : I) : (do let x ← coin p; let y ← coin p; pure (x.toNat + y.toNat)) = binom p 2 := by
  rw [binom_succ, binom_succ, binom_zero]
  simp only [bind_assoc, pure_bind, add_zero]
example (p : I) : (do let x ← coin p; let y ← coin p; let z ← coin p; pure ((x && y) || (x && z) || (y && z))) = (fun n => decide (2 ≤ n)) <$> binom p 3 := by
  rw [binom_succ, binom_succ, binom_succ, binom_zero]
  simp only [map_bind, bind_assoc, pure_bind, map_pure, add_zero]
  congr 1
  funext x
  congr 1
  funext y
  congr 1
  funext z
  cases x <;> cases y <;> cases z <;> rfl

-- World 3
example (p : I) : (do let x ← coin p; let y ← coin p; let z ← coin p; pure (x.toNat + y.toNat + z.toNat)) = binom p 3 := by
  rw [binom_succ, binom_succ, binom_succ, binom_zero]
  simp only [bind_assoc, pure_bind, add_zero, add_assoc]
example (p : I) : Bool.toNat <$> coin p = binom p 1 := by
  rw [binom_succ, binom_zero]
  simp only [pure_bind, add_zero]
  rw [map_eq_pure_bind]
example (p : I) (n : ℕ) : (do let X ← binom p n; let Y ← coin p; pure (X + Y.toNat)) = binom p (n + 1) := by
  induction' n with n ih
  rw [binom_zero, binom_succ, binom_zero]
  simp only [pure_bind, zero_add, add_zero]
  rw [binom_succ p n, binom_succ p (n + 1), ← ih]
  simp only [bind_assoc, pure_bind, add_assoc]
example (p : I) : (fun n => decide (1 ≤ n)) <$> binom p 2 = (do let x ← coin p; let y ← coin p; pure (x || y)) := by
  rw [binom_succ, binom_succ, binom_zero]
  simp only [map_bind, bind_assoc, pure_bind, map_pure, add_zero]
  congr 1
  funext x
  congr 1
  funext y
  cases x <;> cases y <;> rfl
example (p : I) (n m : ℕ) : (do let X ← binom p n; let Y ← binom p m; pure (X + Y)) = binom p (n + m) := by
  induction' m with m ih
  rw [binom_zero]
  simp only [pure_bind, add_zero, bind_pure]
  rw [← binom_succ' p m, ← add_assoc, ← binom_succ' p (n + m), ← ih]
  simp only [bind_assoc, pure_bind, add_assoc]
