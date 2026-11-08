/-!
# World 0, walking on the grid: the rules of the game

The context of world 0, for the board and for the proofs (base: `import
Journal.Notes.DiscreteMeasure.Thinning`, as for the other worlds). A figure walks on the grid
`ℤ × ℤ`. A move is a map `Pos → m Pos` into a monad `m`:

* in `Id`, a move is sure: `north`, `east`, `south`, `west`, and a walk is a program
  `pure (0, 0) >>= north >>= east`, whose normal form is the point where it ends, `pure (1, 1)`;
* in `Set`, a move may go several ways: `step` goes to all four neighbours, and a walk ends in the
  set of the points it can reach. The sure moves are the same maps, now into `Set`.

After each move the game asks Lean for `#simp only [rules] => walk` (the rules: `RULES0` in
`game.js`); the lemmas the proofs use are below, with the monad laws of Lean's core.
-/

namespace ProbGame

/-- A point of the grid. -/
abbrev Pos := ℤ × ℤ

-- `Set` as a monad (in Mathlib only a local instance): `pure a = {a}`, `s >>= f = ⋃ a ∈ s, f a`
attribute [instance] Set.monad

section
variable {m : Type → Type} [Monad m]
/-- One step north, a sure move in any monad. -/
def north : Pos → m Pos | (x, y) => pure (x, y + 1)
/-- One step south. -/
def south : Pos → m Pos | (x, y) => pure (x, y - 1)
/-- One step east. -/
def east : Pos → m Pos | (x, y) => pure (x + 1, y)
/-- One step west. -/
def west : Pos → m Pos | (x, y) => pure (x - 1, y)
end

/-- One step in any direction: the four neighbours. -/
def step : Pos → Set Pos | (x, y) => {(x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1)}

/-- A step east is one of the ways of `step`. -/
theorem step_east (x y : ℤ) : (x + 1, y) ∈ step (x, y) := by simp [step]

/-- A step west is one of the ways of `step`. -/
theorem step_west (x y : ℤ) : (x - 1, y) ∈ step (x, y) := by simp [step]

/-- Where one can be after `n` steps. -/
def walk : ℕ → Set Pos
  | 0 => pure (0, 0)
  | n + 1 => walk n >>= step

/-- Whether `x + y` is odd: the colour of the field on a chessboard. -/
def odd : Pos → Bool | (x, y) => (x + y) % 2 == 1

theorem walk_zero : walk 0 = pure (0, 0) := rfl

theorem walk_succ (n : ℕ) : walk (n + 1) = walk n >>= step := rfl

/-- Reachable: there is a point of `s` from which `f` reaches `b`. -/
theorem mem_bind {α β : Type} (s : Set α) (f : α → Set β) (b : β) : b ∈ s >>= f ↔ ∃ a ∈ s, b ∈ f a := by
  simp [Set.bind_def]

/-- A step changes the colour of the field, whichever way it goes. -/
theorem odd_step (p : Pos) : odd <$> step p = pure (!odd p) := by
  obtain ⟨x, y⟩ := p
  ext b
  simp only [step, odd, Set.fmap_eq_image, Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.pure_def]
  have h1 : (x + 1 + y) % 2 = (x - 1 + y) % 2 := by omega
  have h2 : (x + (y + 1)) % 2 = (x + 1 + y) % 2 := by omega
  have h3 : (x + (y - 1)) % 2 = (x + 1 + y) % 2 := by omega
  rw [h1] at *; rw [h2, h3]
  simp only [or_self]
  rcases Int.emod_two_eq_zero_or_one (x + y) with h | h <;>
  · have : (x - 1 + y) % 2 = 1 - (x + y) % 2 := by omega
    rw [this, h]; rfl

/-- What lies in `s` lies, moved by `f`, in `f <$> s`. -/
theorem mem_map {α β : Type} (f : α → β) {a : α} {s : Set α} (h : a ∈ s) : f a ∈ f <$> s :=
  Set.mem_image_of_mem f h

/-- Two moves are one move. -/
theorem map_map {m : Type → Type} [Monad m] [LawfulMonad m] {α β γ : Type} (μ : m α) (f : α → β) (g : β → γ) :
    g <$> (f <$> μ) = (fun x => g (f x)) <$> μ := (comp_map f g μ).symm

/-! The lemmas the player proves; the game unlocks each after its level. -/

/-- Walking on the Grid, *Colours*: after a step, the colours of all points have changed. -/
theorem odd_bind_step (μ : Set Pos) : odd <$> (μ >>= step) = not <$> (odd <$> μ) := by
  rw [map_bind]
  simp only [odd_step]
  rw [map_map, map_eq_pure_bind]

/-- World 0, the boss: after `n` steps, all points have the colour of `n`. -/
theorem odd_walk (n : ℕ) : odd <$> walk n = pure n.bodd := by
  induction' n with n ih
  · rw [walk_zero, map_pure]
    rfl
  · rw [walk_succ, odd_bind_step, ih, map_pure, Nat.bodd_succ]

/-! For the board: the normal form of a walk in `Set` as a list of points. -/

theorem singleton_bind {α β : Type} (a : α) (f : α → Set β) : ({a} : Set α) >>= f = f a := pure_bind a f

theorem insert_bind {α β : Type} (a : α) (s : Set α) (f : α → Set β) :
    (insert a s : Set α) >>= f = f a ∪ (s >>= f) := by
  ext; simp [Set.bind_def, Set.mem_iUnion]

end ProbGame

open ProbGame
