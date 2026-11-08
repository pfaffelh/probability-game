/-!
# Solutions of TwoCoins: the proofs of its levels, as a player types them, line by line

Checked with `Lean/Rules.lean` in front (`./check-proofs.sh`); `tests/proofs.py` plays them through
the bridge, as the game does.
-/

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
example (p : I) : (do let x ← coin p; pure (x || !x)) = pure true := by
  simp only [Bool.or_not_self]
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
example (p : I) : (do let x ← coin p; let y ← coin p; let z ← coin p; pure (x.toNat + y.toNat + z.toNat)) = binom p 3 := by
  rw [binom_succ, binom_succ, binom_succ, binom_zero]
  simp only [bind_assoc, pure_bind, add_zero, add_assoc]
example (p : I) (n : ℕ) : (do let X ← binom p n; let Y ← coin p; pure (X + Y.toNat)) = binom p (n + 1) := by
  induction' n with n ih
  rw [binom_zero, binom_succ, binom_zero]
  simp only [pure_bind, zero_add, add_zero]
  rw [binom_succ p n, binom_succ p (n + 1), ← ih]
  simp only [bind_assoc, pure_bind, add_assoc]
example (p : I) (n m : ℕ) : (do let X ← binom p n; let Y ← binom p m; pure (X + Y)) = binom p (n + m) := by
  induction' m with m ih
  rw [binom_zero]
  simp only [pure_bind, add_zero, bind_pure]
  rw [← binom_succ' p m, ← add_assoc, ← binom_succ' p (n + m), ← ih]
  simp only [bind_assoc, pure_bind, add_assoc]
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
