import Lake
open Lake DSL

require verso from git "https://github.com/leanprover/verso.git" @ "v4.34.0"

package probgame where

-- The game, embedded with `include_str`; listed so that changes trigger a rebuild.
input_file gameJs where
  path := "ProbGame/game.js"

input_file gameCss where
  path := "ProbGame/game.css"

-- The Lean contexts of the worlds (`Lean/*.lean`), read when the levels are elaborated.
input_dir contexts where
  path := "Lean"
  text := true

lean_lib ProbGame where
  needs := #[gameJs, gameCss, contexts]

@[default_target]
lean_exe probgame where
  root := `Main
