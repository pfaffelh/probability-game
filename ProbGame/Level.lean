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
/-- The rules of world 0, walking on the grid: the context of its board and of its proofs. -/
def world0Rules : String := include_str "../Lean/World0.lean"
/-- The rules of the first world, true and false: the context of its board and of its proofs. -/
def boolRules : String := include_str "../Lean/WorldBool.lean"
/-- The rules of the proofs: the context in which the levels are proved. -/
def proofRules : String := include_str "../Lean/Rules.lean"

/-- The attributes of the proof of a level: its number (`"2.3"`, which decides what is unlocked),
its statement (binders and type, for `example`), the name of the lemma it becomes, and the rules. -/
def proofAttrs (no proof lemma : String) (context := proofRules) : Array (String × String) :=
  if proof.isEmpty then #[] else
    #[("data-no", no), ("data-proof", proof), ("data-lemma", lemma), ("data-proof-context", context)]

-- A level: the distribution at the start, the target, the moves offered, and the Lean statement;
-- `leanStart` and `leanTarget` are the start and the target as `DiscreteMeasure`s, which Lean
-- compares after normalising them with the rules of the world (`context`).
block_extension Block.level (start target moves lean leanStart leanTarget no proof lemma : String) where
  data := Json.mkObj [("start", start), ("target", target), ("moves", moves), ("lean", lean),
    ("leanStart", leanStart), ("leanTarget", leanTarget), ("no", no), ("proof", proof), ("lemma", lemma)]
  traverse _ _ _ := pure none
  extraJs := {JS.mk gameJs}
  extraCss := {CSS.mk gameCss}
  toHtml := some fun _ goB _ data content => do
    let get (k : String) := (data.getObjValAs? String k).toOption.getD ""
    pure <| .tag "div" (#[("class", "pg-level"), ("data-start", get "start"), ("data-target", get "target"),
        ("data-moves", get "moves"), ("data-lean", get "lean"), ("data-lean-start", get "leanStart"),
        ("data-lean-target", get "leanTarget"), ("data-context", world1Rules)] ++ proofAttrs (get "no") (get "proof") (get "lemma")) <|
      .seq #[.tag "div" #[("class", "pg-text")] (← content.mapM goB), .tag "div" #[("class", "pg-board")] .empty]
  toTeX := none

structure LevelConfig where
  start : String
  target : String
  moves : String
  lean : String
  leanStart : String
  leanTarget : String
  no : String
  proof : String
  lemma : String

instance : FromArgs LevelConfig DocElabM where
  fromArgs := LevelConfig.mk <$> .named `start .string false <*> .named `target .string false <*>
    .named `moves .string false <*> .namedD `lean .string "" <*> .namedD `leanStart .string "coin p" <*>
    .namedD `leanTarget .string "" <*> .namedD `no .string "" <*> .namedD `proof .string "" <*> .namedD `lemma .string ""

/-- A level of the probability game; see the module documentation. -/
@[directive]
def level : DirectiveExpanderOf LevelConfig
  | cfg, contents => do
    let blocks ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other (Block.level $(quote cfg.start) $(quote cfg.target) $(quote cfg.moves) $(quote cfg.lean)
        $(quote cfg.leanStart) $(quote cfg.leanTarget) $(quote cfg.no) $(quote cfg.proof) $(quote cfg.lemma))
        #[$blocks,*])

-- A level of the building site: the target, the functions offered and the number of coins allowed
-- (`""`: as many as wanted), or else the sources offered with their numbers (`"coin:1, binom2:2"`). The player lays down coins and applies functions to them, into a network
-- that runs into the target; `game.js` checks it exactly, for every `p`.
block_extension Block.build (target moves coins sources no proof lemma : String) where
  data := Json.mkObj [("target", target), ("moves", moves), ("coins", coins), ("sources", sources),
    ("no", no), ("proof", proof), ("lemma", lemma)]
  traverse _ _ _ := pure none
  extraJs := {JS.mk gameJs}
  extraCss := {CSS.mk gameCss}
  toHtml := some fun _ goB _ data content => do
    let get (k : String) := (data.getObjValAs? String k).toOption.getD ""
    pure <| .tag "div" (#[("class", "pg-level pg-build"), ("data-target", get "target"), ("data-moves", get "moves"),
        ("data-coins", get "coins"), ("data-sources", get "sources")] ++ proofAttrs (get "no") (get "proof") (get "lemma")) <|
      .seq #[.tag "div" #[("class", "pg-text")] (← content.mapM goB), .tag "div" #[("class", "pg-board")] .empty]
  toTeX := none

structure BuildConfig where
  target : String
  moves : String
  coins : String
  sources : String
  no : String
  proof : String
  lemma : String

instance : FromArgs BuildConfig DocElabM where
  fromArgs := BuildConfig.mk <$> .named `target .string false <*> .named `moves .string false <*>
    .namedD `coins .string "" <*> .namedD `sources .string "" <*>
    .namedD `no .string "" <*> .namedD `proof .string "" <*> .namedD `lemma .string ""

/-- A level of the building site: `::::build (target := "bool true:p^2 false:1-p^2") (moves := "and, or, not")
(coins := "2")`, or with other sources: `(sources := "coin:1, binom2:2")`; the functions are those of
`FUNS` in `game.js`, the sources those of `source`. -/
@[directive]
def build : DirectiveExpanderOf BuildConfig
  | cfg, contents => do
    let blocks ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other (Block.build $(quote cfg.target) $(quote cfg.moves) $(quote cfg.coins) $(quote cfg.sources)
        $(quote cfg.no) $(quote cfg.proof) $(quote cfg.lemma)) #[$blocks,*])

-- A level of world 0, walking on the grid: the figure starts at `start` (`"0,0"`), the target is a
-- point or a set of points (`"1,1"`, `"2,0 0,0 1,1 1,-1"`), the moves are `north, east, south, west`
-- and `step` (all four ways), `walls` are fields the figure cannot enter. In the monad `Id` the
-- figure is at one point; in `Set` it is at all the points it can reach. `colours := "yes"` draws
-- the grid as a chessboard. Lean normalises the walk after each move, in `Lean/World0.lean`.
block_extension Block.walk (monad start target moves walls colours no proof lemma : String) where
  data := Json.mkObj [("monad", monad), ("start", start), ("target", target), ("moves", moves), ("walls", walls),
    ("colours", colours), ("no", no), ("proof", proof), ("lemma", lemma)]
  traverse _ _ _ := pure none
  extraJs := {JS.mk gameJs}
  extraCss := {CSS.mk gameCss}
  toHtml := some fun _ goB _ data content => do
    let get (k : String) := (data.getObjValAs? String k).toOption.getD ""
    pure <| .tag "div" (#[("class", "pg-level pg-walk"), ("data-monad", get "monad"), ("data-start", get "start"),
        ("data-target", get "target"), ("data-moves", get "moves"), ("data-walls", get "walls"),
        ("data-colours", get "colours"), ("data-context", world0Rules)] ++
        proofAttrs (get "no") (get "proof") (get "lemma") world0Rules) <|
      .seq #[.tag "div" #[("class", "pg-text")] (← content.mapM goB), .tag "div" #[("class", "pg-board")] .empty]
  toTeX := none

structure WalkConfig where
  monad : String
  start : String
  target : String
  moves : String
  walls : String
  colours : String
  no : String
  proof : String
  lemma : String

instance : FromArgs WalkConfig DocElabM where
  fromArgs := WalkConfig.mk <$> .namedD `monad .string "Id" <*> .namedD `start .string "0,0" <*>
    .named `target .string false <*> .named `moves .string false <*> .namedD `walls .string "" <*>
    .namedD `colours .string "" <*> .namedD `no .string "" <*> .namedD `proof .string "" <*> .namedD `lemma .string ""

/-- A level of world 0: `::::walk (monad := "Set") (target := "1,0 -1,0 0,1 0,-1") (moves := "step")`. -/
@[directive]
def walk : DirectiveExpanderOf WalkConfig
  | cfg, contents => do
    let blocks ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other (Block.walk $(quote cfg.monad) $(quote cfg.start) $(quote cfg.target) $(quote cfg.moves)
        $(quote cfg.walls) $(quote cfg.colours) $(quote cfg.no) $(quote cfg.proof) $(quote cfg.lemma)) #[$blocks,*])

-- A level of the first world: a coin lies surely on one side, for each value of `inputs` ("true",
-- or "false true" for every `b`), and the moves are maps `Bool → Bool`; the level is solved when
-- each row lies on its value of `target` (after exactly `count` moves, when it is given).
block_extension Block.bool (inputs target moves count no proof lemma : String) where
  data := Json.mkObj [("inputs", inputs), ("target", target), ("moves", moves), ("count", count),
    ("no", no), ("proof", proof), ("lemma", lemma)]
  traverse _ _ _ := pure none
  extraJs := {JS.mk gameJs}
  extraCss := {CSS.mk gameCss}
  toHtml := some fun _ goB _ data content => do
    let get (k : String) := (data.getObjValAs? String k).toOption.getD ""
    pure <| .tag "div" (#[("class", "pg-level pg-bool"), ("data-inputs", get "inputs"), ("data-target", get "target"),
        ("data-moves", get "moves"), ("data-count", get "count"), ("data-context", boolRules)] ++
        proofAttrs (get "no") (get "proof") (get "lemma") boolRules) <|
      .seq #[.tag "div" #[("class", "pg-text")] (← content.mapM goB), .tag "div" #[("class", "pg-board")] .empty]
  toTeX := none

structure BoolConfig where
  inputs : String
  target : String
  moves : String
  count : String
  no : String
  proof : String
  lemma : String

instance : FromArgs BoolConfig DocElabM where
  fromArgs := BoolConfig.mk <$> .namedD `inputs .string "true" <*> .named `target .string false <*>
    .named `moves .string false <*> .namedD `count .string "" <*> .namedD `no .string "" <*>
    .namedD `proof .string "" <*> .namedD `lemma .string ""

/-- A level of the first world: `::::boolean (inputs := "false true") (target := "true true") (moves := "not, false")`. -/
@[directive]
def boolean : DirectiveExpanderOf BoolConfig
  | cfg, contents => do
    let blocks ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other (Block.bool $(quote cfg.inputs) $(quote cfg.target) $(quote cfg.moves)
        $(quote cfg.count) $(quote cfg.no) $(quote cfg.proof) $(quote cfg.lemma)) #[$blocks,*])

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

-- The text of the proof of a level, in one language: `:::proofen` and `:::proofde` (inside the
-- level); `game.js` shows it in the proof, below the board.
block_extension Block.proofLang (lang : String) where
  data := Json.str lang
  traverse _ _ _ := pure none
  extraJs := {JS.mk gameJs}
  extraCss := {CSS.mk gameCss}
  toHtml := some fun _ goB _ data content => do
    let lang := data.getStr?.toOption.getD "en"
    pure <| .tag "div" #[("class", s!"pg-proof-text pg-lang pg-lang-{lang}"), ("lang", lang)] (← content.mapM goB)
  toTeX := none

/-- The English text of the proof of a level. -/
@[directive]
def proofen : DirectiveExpanderOf Unit
  | (), contents => do
    let blocks ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other (Block.proofLang "en") #[$blocks,*])

/-- The German text of the proof of a level. -/
@[directive]
def proofde : DirectiveExpanderOf Unit
  | (), contents => do
    let blocks ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other (Block.proofLang "de") #[$blocks,*])

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
