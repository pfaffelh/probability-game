/-!
# World 1, one coin: the rules of the game

The context in which the moves of world 1 are normalised (base: `DiscreteMeasure` of the journal,
`import Journal.Notes.DiscreteMeasure.Thinning`). After each move the game asks Lean for
`#simp only [rules] => state`; the rules are the lemmas below and those of `DiscreteMeasure`
(`coin_not'`, `map_pure`), in the form the moves produce (`fun _ => b`, `fun x => x`).
-/

open MeasureTheory DiscreteMeasure unitInterval

namespace ProbGame

/-- Doing nothing. -/
theorem map_fun_id {α : Type*} (μ : DiscreteMeasure α) : μ.map (fun x => x) = μ := DiscreteMeasure.id_map μ

/-- A constant map sends all the mass to one point: a point mass. -/
theorem coin_map_const {β : Type} (p : unitInterval) (b : β) : (coin p).map (fun _ => b) = pure b := by
  rw [map_eq_map, map_eq_pure_bind]
  exact bind_const_of_hasSum (hasSum_coin p) _

end ProbGame
