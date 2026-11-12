# The Probability Game

Three editions, one branch each (see [BRANCHES.md](BRANCHES.md)): `main`, the game in development
(chance, with the proofs), `monad` (`main` and the other monads: the grid), `show` (the boards alone,
without Lean and without proofs). Online at `/main/`, `/monad/`, `/show/` of
https://lean.mathematik.uni-freiburg.de.

Distributions as bar charts. A distribution (a probability measure, in Lean a `DiscreteMeasure`) is
drawn as a bar over each point of its space, as high as the point's mass; a *move* applies a map to
it, the mass of each point goes to its image (animated), and where several points have the same image
the masses add up. The new distribution is the *image measure* (pushforward)
$P \circ f^{-1}$. Tapping a bar shows its preimage.

Every level has two parts, as in the Natural Number Game: first the **statement**, found on the board
(the distribution is the target, checked exactly for every $p$, the masses being polynomials in $p$); then
the **proof** in Lean, one tactic after another, with an inventory of tactics and theorems that
grows from level to level. A few rules are given (as Peano's axioms in the NNG: `bool_ext` (a
distribution on `Bool` is fixed by its mass at `true`), `map_true` (where the mass of a move goes),
`coin_true`, `coin_false`, `coin_total`, `pure_true`, `coin_and` (independence), the monad laws, the definition of `binom` by
`binom_zero` and `binom_succ`); the lemmas the player proves (`coin_not_true`, `coin_const`, `coin_not`,
the boss of world 1, `binom_one`, `binom_succ'`, `binom_add`) are unlocked after their levels. The proofs
have no `simp`: it only normalises the board. A level's dot is half green after the board, green after the proof.

**True and false** (the first world, before chance; `::::boolean`, `Lean/WorldBool.lean`): a coin
lies surely on one side, once or for every `b` (two rows); the moves are the maps `Bool → Bool`
(`not`, always `true`, always `false`), and Lean normalises the value or the map after each move.
The proofs: `(!true) = false` by `rfl`, rewriting with `Bool.not_true`, then `decide`, which does
the computing in `Bool` (`decide +revert` for `!(!b) = b`, the player's `Bool.not_not`, checks both
values of `b`; `cases b` by hand), `not ∘ not = id` by `decide`, a hypothesis in `rw`; the boss is
`f (f (f b)) = f b` for every `f : Bool → Bool`, by `decide +revert`: four maps, eight cases. Its levels (`::::boolean`) have an inventory of their own.

**Walking on the grid** (branch `monad` only, before chance; `::::walk`, `Lean/WorldWalk.lean`): a figure on
$\mathbb{Z} \times \mathbb{Z}$, the moves `north`, `east`, `south`, `west` as maps `Pos → m Pos`
into a monad, a walk as the program `pure (0, 0) >>= north >>= east`. First in `Id` (sure moves:
one step, around the corner, the other way past a wall); then in `Set`, where `step` goes all four
ways and the figure is the set of the points it can reach (everywhere at once; back home after two
steps, `mem_bind`; the colours of a chessboard, `odd_bind_step`; boss: after $n$ steps all points
have the colour of $n$, `odd_walk`, by induction; never home after five steps). Lean normalises the
walk after each move to `pure (x, y)` or a set of points, which the board reads back. The grid has
an inventory of its own (`w0` in `INVENTORY`); its proofs use only the monad laws and `odd_step`, so
that they carry over to the random walk.

**One coin** (`coin p` at the start, sides `false`/`true` as in Lean): `not`; always `true` (a point mass); surely `false`
without "always `false`" (a composition); `toNat` (to ℕ); the order matters; a bet
(+5 / −2, to ℤ); the better bet; surely zero. The proofs: `rw`, `rfl`, `congr`, `funext`, `cases`.

**Draw, then compute** — a move is a draw and a computation, `f <$> μ = do let x ← μ; pure (f x)`; on
the board of *One coin*, the proofs learn the monad laws for `DiscreteMeasure` before the circuits need
them: `map_eq_pure_bind`, `pure_bind`, `bind_pure`, `bind_assoc` (with `simp only`, which rewrites
inside `do` blocks), `bind_map_left`, a draw that is not used; boss: three flips (in exactly three
moves).

**Building with coins** — a circuit: a line per coin (or $B(n, p)$) and result, a column per
function with dots on its inputs; a coin may feed several functions. Both `true` ($p^2$); first
`true`, then `false`; at least one; surely `false` and surely `true` with one coin; exactly one; the
number of `true` ($B(2, p)$); three coins ($B(3, p)$); $B(2, p)$ and a coin (`binom_succ'`, by
induction); $B(2, p) * B(2, p) = B(4, p)$, proved for all $n$, $m$ (`binom_add`, by induction);
boss: the majority of three. The proofs: `do` blocks, independence (`coin_and`), `simp only` under
binders, `<;>`, the definition of `binom`, induction.

## How it is played

A world's page is a *stage* as high as the screen, as in the
[Incredible Proof Machine](https://github.com/pfaffelh/ipm): one level at a time, nothing to scroll.
On top the world, the name of the level and a dot per level (← → go to the previous and next
level); in the middle the board, with the moves (or building blocks) in a column beside it (below
it on phones), or the proof once the board is solved; below, a line that says what to do next, and
the tool bar: Undo, Start over, Lean (what Lean makes of the board), Tips, Proof/Board, Next (at the
last level: the next world). On phones the tool bar is one row of symbols at the bottom. There is
no text above the board: a level's text is under *Tips* and appears once, when the level is first
played (with the text of the world at the first level), together with the moves new in the level,
drawn as maps; the text of a proof appears when the proof is first opened, with the tactics and
rules new in it. The proof has the inventory in a column beside it (below on phones).
`tests/stage.mjs` checks the stage on every world in five screen sizes.

In place of the table of contents, a *map of the worlds*: a circle per world with the share of its
levels done (☰ on phones). The front page has one big button, *Start* or *Continue* (where one left
off). The *lexicon* (`ProbGame/Lexicon.lean`, filled by `game.js`) shows every move and building
block with its picture, and every tactic and rule, of the worlds of the edition.

## How it works

* The site is a static [Verso](https://github.com/leanprover/verso) document (Lean v4.34.0, the
  Verso of the IPM); `::::level (start := …) (target := …) (moves := …) (lean := …)` is a level
  (`ProbGame/Level.lean`), with `:::en` and `:::de` texts.
* `ProbGame/game.js` plays it in the browser: exact fractions, the moves as maps, the pushforward,
  the animation, the preimage of a tapped bar, the Lean expression of the moves played, one
  level at a time with a dot per level, progress in the browser, English or German (the switch EN | DE in the header, as in the IPM; texts in `:::en` and `:::de`, headings translated by `game.js`).
* The Lean statements of the levels are in `Proofs/` and checked against Mathlib with
  `./check-proofs.sh [project with Mathlib]` (default `~/Code/lean/journal`; also checked with
  nng4's Mathlib). The game needs no Lean while it is played.
* In Mathlib v4.34, `PMF.bernoulli` is deprecated in favour of `ProbabilityTheory.bernoulliMeasure`;
  the proofs still use `PMF` (they work with both versions).

## The proofs

* `Lean/Rules.lean` is the context of the proofs: the rules, stated with `coin p`, `binom p n`,
  `pure`, `do` and `<$>`, proved from the journal, and the lemmas of the player. The bridge loads it
  once (`/start` with the context and `example <statement>`) and checks a proof line by line
  (`/check`).
* A level is one block, with all that belongs to it, and no number:

  ```
  ::::level (start := "bernoulli p") (target := "pure true") (moves := "not, heads")
      (proof := "(p : I) (b : Bool) : (fun _ => b) <$> coin p = pure b") (lemma := "coin_const")
      (new := "apply, bool_ext") (play := "heads")
  :::en … ::: :::de … :::            the texts of the board
  :::proofen … ::: :::proofde … :::  the texts of the proof (a paragraph *Tip.* … is folded)
  :::solution
  ```
  apply bool_ext
  …
  ```
  :::
  ::::
  ```

  `new` is what the level brings into the inventory; `lemma` the lemma it becomes (for the levels
  after it); `play` the moves that solve its board (for `::::build`: steps `M1 M2 and; Z1 not`, the
  lines by their names); `:::solution` its proof as a player types it. The solution is not in the
  page; the tests read it from the source (`tests/levels.py`).
* The inventory of a level is what the levels before it in its group brought (`chance`; `bool` for
  *True and False*, `walk` for *Walking on the Grid*): Verso's traverse pass collects it
  (`ProbGame/Level.lean`), so that a level can be moved or removed alone. `INVENTORY` in `game.js`
  only says what each tactic, rule and lemma is; a line is refused before Lean sees it when it uses
  a tactic or theorem that is not in the inventory (or anything from Mathlib or the journal by its
  full name). Texts refer to levels by their names, not by numbers.
* A world `W` is `ProbGame/Worlds/W.lean` and, if it has rules of its own, `Lean/WorldW.lean`.
  `./check-proofs.sh` checks every solution with Lean, `python3 -I tests/proofs.py` plays them
  through the bridge, `node tests/play.mjs` plays the site (`ONLY=<page>` for one world).

## Lean as the referee

The game is built on the journal's `DiscreteMeasure` (`coin p` with `p : unitInterval`, its
complement `σ p`, `binom`, `LawfulMonad`). After each move the game asks Lean for the normal form of
the state: the moves played as a `DiscreteMeasure`, e.g. `((coin p).map not).map Bool.toNat`,
simplified with `#simp only [rules]`; the rules of the coins are `Lean/WorldCoin.lean` and lemmas of
`DiscreteMeasure` (`coin_not'`, `map_pure`). The normal form is shown below the board
(`map Bool.toNat (coin (σ p))`), and a level is solved when the distribution is the target and Lean gives
the state and the target the same normal form, so that it holds for every `p`. Different correct
ways to the target lead to the same normal form; a wrong one does not.

Lean runs in the bridge `server/bridge.py` (copied from nng-verso's `repl/bridge.py`), on the Lean REPL, with
`DiscreteMeasure` as its base:

```bash
cd ~/Code/lean/journal && BASE="import Journal.Notes.DiscreteMeasure.Thinning" \
  REPL=~/Code/lean/repl-v4.34/.lake/build/bin/repl python3 -I ~/Code/lean/probability-game/server/bridge.py 8091
# then the site with ?backend=http://127.0.0.1:8091
```

Without the bridge the boards still play (exactly, for every `p`), with a note that Lean is not
connected; the proofs need it. (The REPL with all of Mathlib loaded needs about 7 GB; `DiscreteMeasure` imports all of
Mathlib, and importing only what it needs would make that much smaller.)

## Building

```bash
lake build && lake exe probgame          # writes the site to _out/html-multi
cd _out/html-multi && python3 -m http.server 8004
./check-proofs.sh                        # the Lean statements, the rules and the solutions
python3 -I tests/proofs.py               # the solutions through the bridge, line by line
node tests/language.mjs                  # EN and DE on every page
node tests/play.mjs [desktop|phone]      # every level in Chrome: board, then proof (playwright-core)
node tests/stage.mjs                     # the stage: tips, tool bar, nothing to scroll, five screen sizes
```

The sites of all three branches, each from a worktree of its own, as on the server:

```bash
server/build-sites.sh ~/pg-sites         # ~/pg-sites/show, main, monad, and allowed.txt for the bridge
cd ~/pg-sites && python3 -m http.server 8004
BASE=http://127.0.0.1:8004/show/ node tests/play.mjs     # the tests of a branch: from its worktree
```

## License

Apache 2.0, see `LICENSE`.
