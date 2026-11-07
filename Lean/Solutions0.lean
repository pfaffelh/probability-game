/-!
# Solutions of world 0: the proofs of the levels, as a player types them, line by line

Checked with `Lean/World0.lean` in front (`./check-proofs.sh`); `tests/proofs.py` plays them through
the bridge, as the game does.
-/

-- World 0
example : (pure (0, 0) >>= north : Id Pos) = pure (0, 1) := by
  rw [pure_bind]
  rw [north]
  rfl
example : (pure (0, 0) >>= north >>= east : Id Pos) = pure (1, 1) := by
  simp only [pure_bind, north, east]
  rfl
example (x y : ℤ) : (pure (x, y) >>= east >>= north : Id Pos) = pure (x, y) >>= north >>= east := by
  simp only [pure_bind, north, east]
example : (pure (0, 0) >>= east >>= step : Set Pos) = {(2, 0), (0, 0), (1, 1), (1, -1)} := by
  simp only [pure_bind, east, step]
  rfl
example : (0, 0) ∈ (pure (0, 0) >>= step >>= step : Set Pos) := by
  rw [mem_bind]
  exists (1, 0)
  constructor
  rw [pure_bind]
  apply step_east
  apply step_west
example (μ : Set Pos) : odd <$> (μ >>= step) = not <$> (odd <$> μ) := by
  rw [map_bind]
  simp only [odd_step]
  rw [map_map, map_eq_pure_bind]
example (n : ℕ) : odd <$> walk n = pure n.bodd := by
  induction' n with n ih
  rw [walk_zero, map_pure]
  rfl
  rw [walk_succ, odd_bind_step, ih, map_pure, Nat.bodd_succ]
example : (0, 0) ∉ walk 5 := by
  intro h
  have h2 := mem_map odd h
  rw [odd_walk] at h2
  cases h2
