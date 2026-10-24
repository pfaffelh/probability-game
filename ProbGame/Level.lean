import VersoManual

/-!
# Levels of the probability game

`::::level (start := "bernoulli p") (target := "bernoulli 1-p") (moves := "not")` embeds a level
for `game.js`: a distribution is shown as columns of sand over the points of its space, and a move
applies a map to it, so that the sand flows to the images: the distribution becomes its image
measure (pushforward). The level is solved when the distribution is the target.

Distributions are written as `bernoulli p`, `pure true`, or as a space with points and masses
`a + b·p` (written `p`, `1-p`, `1/2`, …): `bool true:p false:1-p`, `nat 1:p 0:1-p`, `int 5:p -2:1-p`. The moves are names of the
catalogue in `game.js` (`id`, `not`, `heads`, `tails`, `toNat`, `payoff 5 -2`).

`lean` is the statement of the level in Lean, for every `p` (with Mathlib's `PMF`); it is shown
when the level is solved and proved in `Proofs/`.

````
::::level (start := "bernoulli p") (target := "bernoulli 1-p") (moves := "not")
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
/-- The rules of world 1, the context in which Lean normalises the state after each move. -/
def world1Rules : String := include_str "../Lean/World1.lean"

-- A level: the distribution at the start, the target, the moves offered, and the Lean statement;
-- `leanStart` and `leanTarget` are the start and the target as `DiscreteMeasure`s, which Lean
-- compares after normalising them with the rules of the world (`context`).
block_extension Block.level (start target moves lean leanStart leanTarget : String) where
  data := Json.mkObj [("start", start), ("target", target), ("moves", moves), ("lean", lean),
    ("leanStart", leanStart), ("leanTarget", leanTarget)]
  traverse _ _ _ := pure none
  extraJs := {JS.mk gameJs}
  extraCss := {CSS.mk gameCss}
  toHtml := some fun _ goB _ data content => do
    let get (k : String) := (data.getObjValAs? String k).toOption.getD ""
    pure <| .tag "div" #[("class", "pg-level"), ("data-start", get "start"), ("data-target", get "target"),
        ("data-moves", get "moves"), ("data-lean", get "lean"), ("data-lean-start", get "leanStart"),
        ("data-lean-target", get "leanTarget"), ("data-context", world1Rules)] <|
      .seq #[.tag "div" #[("class", "pg-text")] (← content.mapM goB), .tag "div" #[("class", "pg-board")] .empty]
  toTeX := none

structure LevelConfig where
  start : String
  target : String
  moves : String
  lean : String
  leanStart : String
  leanTarget : String

instance : FromArgs LevelConfig DocElabM where
  fromArgs := LevelConfig.mk <$> .named `start .string false <*> .named `target .string false <*>
    .named `moves .string false <*> .namedD `lean .string "" <*> .namedD `leanStart .string "coin p" <*>
    .namedD `leanTarget .string ""

/-- A level of the probability game; see the module documentation. -/
@[directive]
def level : DirectiveExpanderOf LevelConfig
  | cfg, contents => do
    let blocks ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other (Block.level $(quote cfg.start) $(quote cfg.target) $(quote cfg.moves) $(quote cfg.lean)
        $(quote cfg.leanStart) $(quote cfg.leanTarget))
        #[$blocks,*])

-- A level of the building site: the target, the functions offered and the number of coins allowed
-- (`""`: as many as wanted). The player lays down coins and applies functions to them, into a network
-- that runs into the target; `game.js` checks it exactly, for every `p`.
block_extension Block.build (target moves coins : String) where
  data := Json.mkObj [("target", target), ("moves", moves), ("coins", coins)]
  traverse _ _ _ := pure none
  extraJs := {JS.mk gameJs}
  extraCss := {CSS.mk gameCss}
  toHtml := some fun _ goB _ data content => do
    let get (k : String) := (data.getObjValAs? String k).toOption.getD ""
    pure <| .tag "div" #[("class", "pg-level pg-build"), ("data-target", get "target"), ("data-moves", get "moves"),
        ("data-coins", get "coins")] <|
      .seq #[.tag "div" #[("class", "pg-text")] (← content.mapM goB), .tag "div" #[("class", "pg-board")] .empty]
  toTeX := none

structure BuildConfig where
  target : String
  moves : String
  coins : String

instance : FromArgs BuildConfig DocElabM where
  fromArgs := BuildConfig.mk <$> .named `target .string false <*> .named `moves .string false <*>
    .namedD `coins .string ""

/-- A level of the building site: `::::build (target := "bool true:p^2 false:1-p^2") (moves := "and, or, not")
(coins := "2")`; the functions are those of `FUNS` in `game.js`. -/
@[directive]
def build : DirectiveExpanderOf BuildConfig
  | cfg, contents => do
    let blocks ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other (Block.build $(quote cfg.target) $(quote cfg.moves) $(quote cfg.coins)) #[$blocks,*])

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
