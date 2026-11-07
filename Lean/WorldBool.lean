/-!
# True and false: the rules of the game

The context of the first world, for the board and for the proofs (base: `import
Journal.Notes.DiscreteMeasure.Thinning`, as for the other worlds). Nothing is added: the world plays
with `Bool` of Lean's core, and its rules are those of the core (`Bool.not_true`, `Bool.not_false`,
`Bool.not_not`, `Function.comp_apply`, `id_eq`).

A coin lies on the table, surely on one side. A move is a map `Bool → Bool`: `not`, always `true`
(`fun _ => true`), always `false` (`fun _ => false`); these are the four maps `Bool → Bool`, with `id`,
and the moves of the coins in the worlds after this one. After each move the game asks Lean for
`#simp only [id_eq, Bool.not_not, Bool.not_true, Bool.not_false] => id e` (`RULESB` in `game.js`),
where `e` is the value (`!(!true)`) or the map (`fun (b : Bool) => !(!b)`); `id` makes sure that
`simp` has something to do.
-/
