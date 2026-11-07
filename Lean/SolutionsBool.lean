/-!
# Solutions of the first world, true and false: the proofs of the levels, as a player types them

Checked with `Lean/WorldBool.lean` in front (`./check-proofs.sh`); `tests/proofs.py` plays them
through the bridge, as the game does.
-/

-- True and false
example : (!true) = false := by
  rfl
example : (!(!true)) = true := by
  rw [Bool.not_true, Bool.not_false]
example (b : Bool) : (!((fun _ => false) b)) = true := by
  rfl
example (b : Bool) : (!(!b)) = b := by
  cases b
  rfl
  rfl
example : not ∘ not = (id : Bool → Bool) := by
  funext b
  rw [Function.comp_apply, Bool.not_not, id_eq]
example (f : Bool → Bool) (h : f true = true) : f (f true) = true := by
  rw [h, h]
example (f : Bool → Bool) (b : Bool) : f (f (f b)) = f b := by
  cases b
  cases h : f false
  rw [h, h]
  cases h2 : f true
  rw [h]
  rw [h2]
  cases h : f true
  cases h2 : f false
  rw [h2]
  rw [h]
  rw [h, h]
