/-!
# Solutions of OneCoin: the proofs of its levels, as a player types them, line by line

Checked with `Lean/Rules.lean` in front (`./check-proofs.sh`); `tests/proofs.py` plays them through
the bridge, as the game does.
-/

example (p : I) : (not <$> coin p) true = σ p := by
  rw [map_true]
  rw [Bool.not_true, Bool.not_false]
  rw [Bool.cond_false, Bool.cond_true, zero_add]
  rw [coin_false]
example (p : I) (b : Bool) : (fun _ => b) <$> coin p = pure b := by
  apply bool_ext
  rw [map_true, pure_true]
  cases b
  rw [Bool.cond_false, Bool.cond_false, Bool.cond_false, zero_add]
  rw [Bool.cond_true, Bool.cond_true, Bool.cond_true, coin_total]
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
example (p : I) : Bool.toNat <$> ((fun _ => false) <$> coin p) = pure 0 := by
  rw [coin_const, map_pure]
  rfl
example (p : I) : not <$> coin p = coin (σ p) := by
  apply bool_ext
  rw [coin_not_true, coin_true]
