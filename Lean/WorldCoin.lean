/-!
# World 1, one coin: the rules of the game

The context in which the moves of world 1 are normalised (base: Mathlib's `PMF`; not used by a world
of this branch). After each move the game asks Lean for
`#simp only [rules] => state`; the rules are the lemmas below and `PMF.pure_map`, in the form the moves produce (`fun _ => b`, `fun x => x`).
-/

open unitInterval

namespace ProbGame

/-- Doing nothing. -/
theorem map_fun_id {α : Type} (μ : PMF α) : μ.map (fun x => x) = μ := PMF.map_id μ

/-- A constant map sends all the mass to one point: a point mass. -/
theorem map_const_pure {α β : Type} (μ : PMF α) (b : β) : μ.map (fun _ => b) = PMF.pure b :=
  PMF.map_const μ b

end ProbGame
