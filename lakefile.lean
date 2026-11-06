import Lake
open Lake DSL

require verso from git "https://github.com/leanprover/verso.git" @ "v4.34.0"

package probgame where

-- The game, embedded with `include_str`; listed so that changes trigger a rebuild.
input_file gameJs where
  path := "ProbGame/game.js"

input_file gameCss where
  path := "ProbGame/game.css"

input_file world1Rules where
  path := "Lean/World1.lean"

input_file world0Rules where
  path := "Lean/World0.lean"

lean_lib ProbGame where
  needs := #[gameJs, gameCss, world0Rules, world1Rules]

@[default_target]
lean_exe probgame where
  root := `Main
