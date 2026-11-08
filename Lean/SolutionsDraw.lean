/-!
# Solutions of Draw, then Compute: the proofs of its levels, as a player types them, line by line

Checked with `Lean/Rules.lean` in front (`./check-proofs.sh`); `tests/proofs.py` plays them through
the bridge, as the game does.
-/

example (p : I) : (do let x ← coin p; pure (!x)) = not <$> coin p := by
  rw [map_eq_pure_bind]
example : (do let x ← pure true; pure (!x)) = (pure false : DiscreteMeasure Bool) := by
  rw [pure_bind]
  rw [Bool.not_true]
example (p : I) : (coin p >>= fun x => pure x) = coin p := by
  rw [bind_pure]
example (p : I) : (do let y ← (do let x ← coin p; pure (!x)); pure (!y)) = coin p := by
  rw [bind_assoc]
  simp only [pure_bind, Bool.not_not]
  rw [bind_pure]
example (p : I) : (do let x ← not <$> coin p; pure (!x)) = coin p := by
  rw [bind_map_left]
  simp only [Bool.not_not]
  rw [bind_pure]
example (p : I) (b : Bool) : (do let _ ← coin p; pure b) = pure b := by
  rw [← map_eq_pure_bind]
  rw [coin_const]
example (p : I) : (do let y ← (do let x ← coin p; pure (!x)); let z ← pure (!y); pure (!z)) = not <$> coin p := by
  rw [bind_assoc]
  simp only [pure_bind, Bool.not_not]
  rw [map_eq_pure_bind]
