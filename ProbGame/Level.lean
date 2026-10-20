import VersoManual

/-!
# Levels of the probability game

`::::level (start := "bernoulli 1/3") (target := "bernoulli 2/3") (moves := "not")` embeds a level
for `game.js`: a distribution is shown as columns of sand over the points of its space, and a move
applies a map to it, so that the sand flows to the images: the distribution becomes its image
measure (pushforward). The level is solved when the distribution is the target.

Distributions are written as `bernoulli 1/3`, `pure true`, or as a space with points and masses:
`bool true:1/3 false:2/3`, `nat 1:1/3 0:2/3`, `int 5:1/3 -2:2/3`. The moves are names of the
catalogue in `game.js` (`id`, `not`, `heads`, `tails`, `toNat`, `payoff 5 -2`).

`lean` is the statement of the level in Lean, for every `p` (with Mathlib's `PMF`); it is shown
when the level is solved and proved in `Proofs/`.

````
::::level (start := "bernoulli 1/3") (target := "bernoulli 2/3") (moves := "not")
  (lean := "(bernoulli p h).map not = bernoulli (1 - p) _")
:::en
Flip the coin.
:::
::::
````
-/

open Lean Elab
open Verso Doc Elab ArgParse
open Verso.Genre Manual
open Verso.Output (Html)

namespace ProbGame

def gameJs : String := include_str "game.js"
def gameCss : String := include_str "game.css"

-- A level: the distribution at the start, the target, the moves offered, and the Lean statement.
block_extension Block.level (start target moves lean : String) where
  data := Json.mkObj [("start", start), ("target", target), ("moves", moves), ("lean", lean)]
  traverse _ _ _ := pure none
  extraJs := {JS.mk gameJs}
  extraCss := {CSS.mk gameCss}
  toHtml := some fun _ goB _ data content => do
    let get (k : String) := (data.getObjValAs? String k).toOption.getD ""
    pure <| .tag "div" #[("class", "pg-level"), ("data-start", get "start"), ("data-target", get "target"),
        ("data-moves", get "moves"), ("data-lean", get "lean")] <|
      .seq #[.tag "div" #[("class", "pg-text")] (← content.mapM goB), .tag "div" #[("class", "pg-board")] .empty]
  toTeX := none

structure LevelConfig where
  start : String
  target : String
  moves : String
  lean : String

instance : FromArgs LevelConfig DocElabM where
  fromArgs := LevelConfig.mk <$> .named `start .string false <*> .named `target .string false <*>
    .named `moves .string false <*> .namedD `lean .string ""

/-- A level of the probability game; see the module documentation. -/
@[directive]
def level : DirectiveExpanderOf LevelConfig
  | cfg, contents => do
    let blocks ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other (Block.level $(quote cfg.start) $(quote cfg.target) $(quote cfg.moves) $(quote cfg.lean))
        #[$blocks,*])

-- Text in one language: `:::en` and `:::de`; `game.js` shows the language chosen.
block_extension Block.lang (lang : String) where
  data := Json.str lang
  traverse _ _ _ := pure none
  extraJs := {JS.mk gameJs}
  extraCss := {CSS.mk gameCss}
  toHtml := some fun _ goB _ data content => do
    let lang := data.getStr?.toOption.getD "en"
    pure <| .tag "div" #[("class", s!"pg-lang pg-lang-{lang}"), ("lang", lang)] (← content.mapM goB)
  toTeX := none

/-- English text; see `de`. -/
@[directive]
def en : DirectiveExpanderOf Unit
  | (), contents => do
    let blocks ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other (Block.lang "en") #[$blocks,*])

/-- German text, shown instead of the `en` blocks when German is chosen. -/
@[directive]
def de : DirectiveExpanderOf Unit
  | (), contents => do
    let blocks ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other (Block.lang "de") #[$blocks,*])

end ProbGame
