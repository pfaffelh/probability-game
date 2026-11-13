import VersoManual

/-!
# Levels of the probability game

`::::level (start := "bernoulli p") (target := "bernoulli 1-p") (moves := "not")` embeds a level
for `game.js`: a distribution is shown as a bar chart, a bar over each point of its space, and a move
applies a map to it, so that the mass goes to the images: the distribution becomes its image
measure (pushforward). The level is solved when the distribution is the target (in exactly
`count` moves, when it is given).

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

/-- A Lean context of the game (the rules of a world: the board and the proofs are checked in it),
read from its file when the level is elaborated. The worlds name their contexts (`context`,
`proofContext`); `lakefile.lean` lists the folder `Lean/` as an input, so that a change of a context
rebuilds the site. -/
def readContext (path : String) : DocElabM String := do
  match ← (IO.FS.readFile path).toBaseIO with
  | .ok s => pure s
  | .error e => throwError "the context {path} of the level cannot be read: {e}"

/-! ## What a level brings, and what it may use

A level names what it brings into the inventory (`(new := "bool_ext, apply")`) and the lemma it
becomes (`(lemma := "coin_not")`); it has no number. In the traverse pass each level is entered in
`ProbGame.levels`, in the order of the document, with its group (`chance`, `bool` or `walk`: each
group has an inventory of its own). When a level is rendered, its inventory is what the levels of its
group before it brought, and what it brings itself: so a level can be moved or removed alone. -/

/-- The world of a level: the module it is in (`ProbGame.Worlds.OneCoin`), for the tests. -/
def worldOf : DocElabM String := return (← getMainModule).toString

/-- The names in a list `"a, b, c"`. -/
def namesIn (s : String) : Array String :=
  (s.splitOn ",").toArray.map (·.trimAscii.toString) |>.filter (!·.isEmpty)

/-- Enters a level in `ProbGame.levels` (once: the traverse pass runs until nothing changes). -/
def registerLevel {m : Type → Type} [Monad m] [MonadState Manual.TraverseState m] (id : InternalId) (data : Json) : m Unit := do
  let levels : Array Json := match (← get).get? `ProbGame.levels with
    | some (.ok (ls : Array Json)) => ls
    | _ => #[]
  unless levels.any (·.getObjValD "id" == toJson id) do
    let entry := Json.mkObj [("id", toJson id), ("group", data.getObjValD "group"),
      ("new", data.getObjValD "new"), ("lemma", data.getObjValD "lemma")]
    modify (·.set `ProbGame.levels (levels.push entry))

/-- The inventory of the level `id` (what the levels of its group before it brought, and what it
brings itself) and what is new in it, as JSON lists of names. -/
def inventoryOf (id : InternalId) (st : Manual.TraverseState) : String × String := Id.run do
  let levels : Array Json := match st.get? `ProbGame.levels with
    | some (.ok (ls : Array Json)) => ls
    | _ => #[]
  let str (l : Json) (k : String) := (l.getObjValAs? String k).toOption.getD ""
  let some i := levels.findIdx? (·.getObjValD "id" == toJson id) | return ("[]", "[]")
  let me := levels[i]!
  let mut inv : Array String := #[]
  for l in levels.extract 0 i do
    if str l "group" == str me "group" then
      inv := inv ++ namesIn (str l "new") ++ namesIn (str l "lemma")
  let new := namesIn (str me "new")
  return ((toJson (inv ++ new)).compress, (toJson new).compress)

/-- The attributes of the proof of a level: its statement (binders and type, for `example`), the
lemma it becomes, the rules (its context), its group, its inventory and what is new in it. -/
def proofAttrs (id : InternalId) (st : Manual.TraverseState) (data : Json) (context : String) : Array (String × String) :=
  let get (k : String) := (data.getObjValAs? String k).toOption.getD ""
  let (inv, new) := inventoryOf id st
  #[("data-world", get "world"), ("data-group", get "group")] ++
  if (get "proof").isEmpty then #[] else
    #[("data-proof", get "proof"), ("data-lemma", get "lemma"), ("data-proof-context", context),
      ("data-inventory", inv), ("data-new", new)]

/-- The solution of a level: `:::solution` with the proof as a code block, as a player types it. It
is not shown (not even in the page): `check-proofs.sh` and the tests read it from the source. -/
@[directive]
def solution : DirectiveExpanderOf Unit
  | (), _ => ``(Verso.Doc.Block.concat #[])

-- A level: the distribution at the start, the target, the moves offered, and the Lean statement;
-- `leanStart` and `leanTarget` are the start and the target as `DiscreteMeasure`s, which Lean
-- compares after normalising them with the rules of the world (`context`).
block_extension Block.level (start target moves count lean leanStart leanTarget new proof lemma context proofContext world : String) where
  data := Json.mkObj [("start", start), ("target", target), ("moves", moves), ("count", count), ("lean", lean),
    ("leanStart", leanStart), ("leanTarget", leanTarget), ("new", new), ("proof", proof), ("lemma", lemma),
    ("context", context), ("proofContext", proofContext), ("world", world), ("group", "chance")]
  traverse id data _ := do registerLevel id data; pure none
  extraJs := {JS.mk gameJs}
  extraCss := {CSS.mk gameCss}
  toHtml := some fun _ goB id data content => do
    let get (k : String) := (data.getObjValAs? String k).toOption.getD ""
    pure <| .tag "div" (#[("class", "pg-level"), ("data-start", get "start"), ("data-target", get "target"),
        ("data-moves", get "moves"), ("data-count", get "count"), ("data-lean", get "lean"), ("data-lean-start", get "leanStart"),
        ("data-lean-target", get "leanTarget"), ("data-context", get "context")] ++ proofAttrs id (← Doc.Html.HtmlT.state) data (get "proofContext")) <|
      .seq #[.tag "div" #[("class", "pg-text")] (← content.mapM goB), .tag "div" #[("class", "pg-board")] .empty]
  toTeX := none

structure LevelConfig where
  start : String
  target : String
  moves : String
  count : String
  lean : String
  leanStart : String
  leanTarget : String
  new : String
  proof : String
  lemma : String
  context : String
  proofContext : String
  play : String

instance : FromArgs LevelConfig DocElabM where
  fromArgs := LevelConfig.mk <$> .named `start .string false <*> .named `target .string false <*>
    .named `moves .string false <*> .namedD `count .string "" <*> .namedD `lean .string "" <*> .namedD `leanStart .string "coin p" <*>
    .namedD `leanTarget .string "" <*> .namedD `new .string "" <*> .namedD `proof .string "" <*> .namedD `lemma .string "" <*>
    .namedD `context .string "Lean/WorldCoin.lean" <*> .namedD `proofContext .string "Lean/Rules.lean" <*> .namedD `play .string ""

/-- A level of the probability game; see the module documentation. -/
@[directive]
def level : DirectiveExpanderOf LevelConfig
  | cfg, contents => do
    let blocks ← contents.mapM elabBlock
    let context ← readContext cfg.context
    let proofContext ← readContext cfg.proofContext
    let world ← worldOf
    ``(Verso.Doc.Block.other (Block.level $(quote cfg.start) $(quote cfg.target) $(quote cfg.moves) $(quote cfg.count) $(quote cfg.lean)
        $(quote cfg.leanStart) $(quote cfg.leanTarget) $(quote cfg.new) $(quote cfg.proof) $(quote cfg.lemma)
        $(quote context) $(quote proofContext) $(quote world))
        #[$blocks,*])

-- A level of the building site: the target, the functions offered and the number of coins allowed
-- (`""`: as many as wanted), or else the sources offered with their numbers (`"coin:1, binom2:2"`). The player lays down coins and applies functions to them, into a network
-- that runs into the target; `game.js` checks it exactly, for every `p`.
block_extension Block.build (target moves coins sources new proof lemma proofContext world : String) where
  data := Json.mkObj [("target", target), ("moves", moves), ("coins", coins), ("sources", sources),
    ("new", new), ("proof", proof), ("lemma", lemma), ("proofContext", proofContext), ("world", world), ("group", "chance")]
  traverse id data _ := do registerLevel id data; pure none
  extraJs := {JS.mk gameJs}
  extraCss := {CSS.mk gameCss}
  toHtml := some fun _ goB id data content => do
    let get (k : String) := (data.getObjValAs? String k).toOption.getD ""
    pure <| .tag "div" (#[("class", "pg-level pg-build"), ("data-target", get "target"), ("data-moves", get "moves"),
        ("data-coins", get "coins"), ("data-sources", get "sources")] ++ proofAttrs id (← Doc.Html.HtmlT.state) data (get "proofContext")) <|
      .seq #[.tag "div" #[("class", "pg-text")] (← content.mapM goB), .tag "div" #[("class", "pg-board")] .empty]
  toTeX := none

structure BuildConfig where
  target : String
  moves : String
  coins : String
  sources : String
  new : String
  proof : String
  lemma : String
  proofContext : String
  play : String

instance : FromArgs BuildConfig DocElabM where
  fromArgs := BuildConfig.mk <$> .named `target .string false <*> .named `moves .string false <*>
    .namedD `coins .string "" <*> .namedD `sources .string "" <*>
    .namedD `new .string "" <*> .namedD `proof .string "" <*> .namedD `lemma .string "" <*>
    .namedD `proofContext .string "Lean/Rules.lean" <*> .namedD `play .string ""

/-- A level of the building site: `::::build (target := "bool true:p^2 false:1-p^2") (moves := "and, or, not")
(coins := "2")`, or with other sources: `(sources := "coin:1, binom2:2")`; the functions are those of
`FUNS` in `game.js`, the sources those of `source`. -/
@[directive]
def build : DirectiveExpanderOf BuildConfig
  | cfg, contents => do
    let blocks ← contents.mapM elabBlock
    let proofContext ← readContext cfg.proofContext
    let world ← worldOf
    ``(Verso.Doc.Block.other (Block.build $(quote cfg.target) $(quote cfg.moves) $(quote cfg.coins) $(quote cfg.sources)
        $(quote cfg.new) $(quote cfg.proof) $(quote cfg.lemma) $(quote proofContext) $(quote world)) #[$blocks,*])

-- A level of world 0, walking on the grid: the figure starts at `start` (`"0,0"`), the target is a
-- point or a set of points (`"1,1"`, `"2,0 0,0 1,1 1,-1"`), the moves are `north, east, south, west`
-- and `step` (all four ways), `walls` are fields the figure cannot enter. In the monad `Id` the
-- figure is at one point; in `Set` it is at all the points it can reach. `colours := "yes"` draws
-- the grid as a chessboard. Lean normalises the walk after each move, in `Lean/WorldWalk.lean`.
block_extension Block.walk (monad start target moves walls colours new proof lemma context world : String) where
  data := Json.mkObj [("monad", monad), ("start", start), ("target", target), ("moves", moves), ("walls", walls),
    ("colours", colours), ("new", new), ("proof", proof), ("lemma", lemma), ("context", context), ("world", world), ("group", "walk")]
  traverse id data _ := do registerLevel id data; pure none
  extraJs := {JS.mk gameJs}
  extraCss := {CSS.mk gameCss}
  toHtml := some fun _ goB id data content => do
    let get (k : String) := (data.getObjValAs? String k).toOption.getD ""
    pure <| .tag "div" (#[("class", "pg-level pg-walk"), ("data-monad", get "monad"), ("data-start", get "start"),
        ("data-target", get "target"), ("data-moves", get "moves"), ("data-walls", get "walls"),
        ("data-colours", get "colours"), ("data-context", get "context")] ++
        proofAttrs id (← Doc.Html.HtmlT.state) data (get "context")) <|
      .seq #[.tag "div" #[("class", "pg-text")] (← content.mapM goB), .tag "div" #[("class", "pg-board")] .empty]
  toTeX := none

structure WalkConfig where
  monad : String
  start : String
  target : String
  moves : String
  walls : String
  colours : String
  new : String
  proof : String
  lemma : String
  context : String
  play : String

instance : FromArgs WalkConfig DocElabM where
  fromArgs := WalkConfig.mk <$> .namedD `monad .string "Id" <*> .namedD `start .string "0,0" <*>
    .named `target .string false <*> .named `moves .string false <*> .namedD `walls .string "" <*>
    .namedD `colours .string "" <*> .namedD `new .string "" <*> .namedD `proof .string "" <*> .namedD `lemma .string "" <*>
    .namedD `context .string "Lean/WorldWalk.lean" <*> .namedD `play .string ""

/-- A level of world 0: `::::walk (monad := "Set") (target := "1,0 -1,0 0,1 0,-1") (moves := "step")`. -/
@[directive]
def walk : DirectiveExpanderOf WalkConfig
  | cfg, contents => do
    let blocks ← contents.mapM elabBlock
    let context ← readContext cfg.context
    let world ← worldOf
    ``(Verso.Doc.Block.other (Block.walk $(quote cfg.monad) $(quote cfg.start) $(quote cfg.target) $(quote cfg.moves)
        $(quote cfg.walls) $(quote cfg.colours) $(quote cfg.new) $(quote cfg.proof) $(quote cfg.lemma) $(quote context) $(quote world)) #[$blocks,*])

-- A level of the first world: a coin lies surely on one side, for each value of `inputs` ("true",
-- or "false true" for every `b`), and the moves are maps `Bool → Bool`; the level is solved when
-- each row lies on its value of `target` (after exactly `count` moves, when it is given).
block_extension Block.bool (inputs target moves count new proof lemma context world : String) where
  data := Json.mkObj [("inputs", inputs), ("target", target), ("moves", moves), ("count", count),
    ("new", new), ("proof", proof), ("lemma", lemma), ("context", context), ("world", world), ("group", "bool")]
  traverse id data _ := do registerLevel id data; pure none
  extraJs := {JS.mk gameJs}
  extraCss := {CSS.mk gameCss}
  toHtml := some fun _ goB id data content => do
    let get (k : String) := (data.getObjValAs? String k).toOption.getD ""
    pure <| .tag "div" (#[("class", "pg-level pg-bool"), ("data-inputs", get "inputs"), ("data-target", get "target"),
        ("data-moves", get "moves"), ("data-count", get "count"), ("data-context", get "context")] ++
        proofAttrs id (← Doc.Html.HtmlT.state) data (get "context")) <|
      .seq #[.tag "div" #[("class", "pg-text")] (← content.mapM goB), .tag "div" #[("class", "pg-board")] .empty]
  toTeX := none

structure BoolConfig where
  inputs : String
  target : String
  moves : String
  count : String
  new : String
  proof : String
  lemma : String
  context : String
  play : String

instance : FromArgs BoolConfig DocElabM where
  fromArgs := BoolConfig.mk <$> .namedD `inputs .string "true" <*> .named `target .string false <*>
    .named `moves .string false <*> .namedD `count .string "" <*> .namedD `new .string "" <*>
    .namedD `proof .string "" <*> .namedD `lemma .string "" <*> .namedD `context .string "Lean/WorldBool.lean" <*>
    .namedD `play .string ""

/-- A level of the first world: `::::boolean (inputs := "false true") (target := "true true") (moves := "not, false")`. -/
@[directive]
def boolean : DirectiveExpanderOf BoolConfig
  | cfg, contents => do
    let blocks ← contents.mapM elabBlock
    let context ← readContext cfg.context
    let world ← worldOf
    ``(Verso.Doc.Block.other (Block.bool $(quote cfg.inputs) $(quote cfg.target) $(quote cfg.moves)
        $(quote cfg.count) $(quote cfg.new) $(quote cfg.proof) $(quote cfg.lemma) $(quote context) $(quote world)) #[$blocks,*])

-- A circuit: inputs above (`x y`), gates that the player drags onto the board and wires, and an
-- output below. Without coins the target is a truth table (`table := "0110"`: the output for the
-- rows ff, ft, tf, tt), the goal in Lean is `goal` (`x ^^ y`), and the group is that of the first
-- world (`bool`). With coins (`coins := "p p"`: a coin `coin p` at each input) the target is the
-- distribution of the output (`target := "bool true:2p(1-p) false:1-2p(1-p)"`), and the group is
-- that of chance.
block_extension Block.circuit (inputs gates table goal coins target new proof lemma context world shape every : String) where
  data := Json.mkObj [("inputs", inputs), ("gates", gates), ("table", table), ("goal", goal), ("coins", coins),
    ("target", target), ("new", new), ("proof", proof), ("lemma", lemma), ("context", context), ("world", world),
    ("shape", shape), ("every", every), ("group", if coins.isEmpty then "bool" else "chance")]
  traverse id data _ := do registerLevel id data; pure none
  extraJs := {JS.mk gameJs}
  extraCss := {CSS.mk gameCss}
  toHtml := some fun _ goB id data content => do
    let get (k : String) := (data.getObjValAs? String k).toOption.getD ""
    pure <| .tag "div" (#[("class", "pg-level pg-circuit"), ("data-inputs", get "inputs"), ("data-gates", get "gates"),
        ("data-table", get "table"), ("data-goal", get "goal"), ("data-coins", get "coins"), ("data-target", get "target"),
        ("data-shape", get "shape"), ("data-every", get "every")] ++
        proofAttrs id (← Doc.Html.HtmlT.state) data (get "context")) <|
      .seq #[.tag "div" #[("class", "pg-text")] (← content.mapM goB), .tag "div" #[("class", "pg-board")] .empty]
  toTeX := none

structure CircuitConfig where
  inputs : String
  gates : String
  table : String
  goal : String
  coins : String
  target : String
  new : String
  proof : String
  lemma : String
  context : String
  play : String
  shape : String
  every : String

instance : FromArgs CircuitConfig DocElabM where
  fromArgs := CircuitConfig.mk <$> .namedD `inputs .string "x y" <*> .named `gates .string false <*>
    .namedD `table .string "" <*> .namedD `goal .string "" <*> .namedD `coins .string "" <*> .namedD `target .string "" <*>
    .namedD `new .string "" <*> .namedD `proof .string "" <*> .namedD `lemma .string "" <*>
    .namedD `context .string "Lean/WorldBool.lean" <*> .namedD `play .string "" <*>
    .namedD `shape .string "" <*> .namedD `every .string ""

/-- A circuit: `::::circuit (inputs := "x y") (gates := "and, or, not") (table := "0110") (goal := "x ^^ y")`. -/
@[directive]
def circuit : DirectiveExpanderOf CircuitConfig
  | cfg, contents => do
    let blocks ← contents.mapM elabBlock
    let context ← readContext cfg.context
    let world ← worldOf
    ``(Verso.Doc.Block.other (Block.circuit $(quote cfg.inputs) $(quote cfg.gates) $(quote cfg.table) $(quote cfg.goal)
        $(quote cfg.coins) $(quote cfg.target) $(quote cfg.new) $(quote cfg.proof) $(quote cfg.lemma) $(quote context)
        $(quote world) $(quote cfg.shape) $(quote cfg.every)) #[$blocks,*])

-- The lexicon: every move, building block, tactic and rule of the game, which `game.js` writes
-- into this block (`::::lexicon` with no content), from the same tables as the tips.
block_extension Block.lexicon where
  data := Json.null
  traverse _ _ _ := pure none
  extraJs := {JS.mk gameJs}
  extraCss := {CSS.mk gameCss}
  toHtml := some fun _ goB _ _ content => do
    -- the names that the levels of the game bring, for the lexicon of tactics and rules
    let levels : Array Json := match (← Doc.Html.HtmlT.state).get? `ProbGame.levels with
      | some (.ok (ls : Array Json)) => ls
      | _ => #[]
    let str (l : Json) (k : String) := (l.getObjValAs? String k).toOption.getD ""
    let items := levels.foldl (fun acc l => acc ++ namesIn (str l "new") ++ namesIn (str l "lemma")) #[]
    pure <| .tag "div" #[("class", "pg-lexicon"), ("data-items", (toJson items).compress)] (← content.mapM goB)
  toTeX := none

/-- The lexicon of the game, filled by `game.js`. -/
@[directive]
def lexicon : DirectiveExpanderOf Unit
  | (), contents => do
    let blocks ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other Block.lexicon #[$blocks,*])

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

-- What belongs to one edition only (`ProbGame.edition`: `show`, or `main` for the editions with
-- proofs), e.g. a level: `:::::only (edition := "show")` around it. Every edition has the page;
-- `game.js` removes the part in the other editions, before it counts the levels.
block_extension Block.only (edition : String) where
  data := Json.str edition
  traverse _ _ _ := pure none
  extraJs := {JS.mk gameJs}
  extraCss := {CSS.mk gameCss}
  toHtml := some fun _ goB _ data content => do
    let edition := data.getStr?.toOption.getD "main"
    pure <| .tag "div" #[("class", "pg-only"), ("data-edition", edition)] (← content.mapM goB)
  toTeX := none

structure OnlyConfig where
  edition : String

instance : FromArgs OnlyConfig DocElabM where
  fromArgs := OnlyConfig.mk <$> .named `edition .string false

/-- A part of the page for one edition only: `show`, or `main` (the editions with proofs). -/
@[directive]
def only : DirectiveExpanderOf OnlyConfig
  | cfg, contents => do
    let blocks ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other (Block.only $(quote cfg.edition)) #[$blocks,*])

end ProbGame
