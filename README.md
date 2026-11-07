# The Probability Game

Distributions as sand. A distribution is drawn as columns of sand over the points of its space; a
*move* applies a map to it, the sand of each point flows to its image (animated), and where several
points have the same image it piles up. The new distribution is the *image measure* (pushforward)
$P \circ f^{-1}$. Tapping a column shows its preimage.

Every level has two parts, as in the Natural Number Game: first the **statement**, found on the board
(the sand fills the target, checked exactly for every $p$, the masses being polynomials in $p$); then
the **proof** in Lean, one tactic after another, with an inventory of tactics and theorems that
grows from level to level. A few rules are given (as Peano's axioms in the NNG: `bool_ext` (a
distribution on `Bool` is fixed by its mass at `true`), `map_true` (where the sand of a move goes),
`coin_true`, `coin_false`, `coin_total`, `pure_true`, `coin_and` (independence), the monad laws, the definition of `binom` by
`binom_zero` and `binom_succ`); the lemmas the player proves (`coin_not_true`, `coin_const`, `coin_not`,
the boss of world 1, `binom_one`, `binom_succ'`, `binom_add`) are unlocked after their levels. The proofs
have no `simp`: it only normalises the board. A level's dot is half green after the board, green after the proof.

**World 0, walking on the grid** (before chance; `::::walk`, `Lean/World0.lean`): a figure on
$\mathbb{Z} \times \mathbb{Z}$, the moves `north`, `east`, `south`, `west` as maps `Pos → m Pos`
into a monad, a walk as the program `pure (0, 0) >>= north >>= east`. First in `Id` (sure moves:
one step, around the corner, the other way past a wall); then in `Set`, where `step` goes all four
ways and the figure is the set of the points it can reach (everywhere at once; back home after two
steps, `mem_bind`; the colours of a chessboard, `odd_bind_step`; boss: after $n$ steps all points
have the colour of $n$, `odd_walk`, by induction; never home after five steps). Lean normalises the
walk after each move to `pure (x, y)` or a set of points, which the board reads back. World 0 has
an inventory of its own (`w0` in `INVENTORY`); its proofs use only the monad laws and `odd_step`, so
that they carry over to the random walk.

**World 1, one coin** (`coin p` at the start, sides `false`/`true` as in Lean): `not`; always `true` (a point mass); surely `false`
without "always `false`" (a composition); `toNat` (to ℕ); the order matters; a bet
(+5 / −2, to ℤ); the better bet; surely zero. The proofs: `rw`, `rfl`, `congr`, `funext`, `cases`.

**World 2, building with coins** — a circuit: a line per coin and result, a column per function with
dots on its inputs; a coin may feed several functions. Both `true` ($p^2$); first `true`, then
`false`; at least one; surely `false` with one coin; exactly one; the number of `true` ($B(2, p)$);
boss: the majority of three. The proofs: `do` blocks, independence (`coin_and`), `simp only` under
binders, `<;>`, the definition of `binom`.

**World 3, counting** — `B(n, p)` as a building block. Three coins; $B(1, p)$ (`binom_one`);
$B(2, p)$ and a coin (`binom_succ'`, by induction); at least $1$ out of $B(2, p)$; boss:
$B(2, p) * B(2, p) = B(4, p)$, proved for all $n$, $m$ (`binom_add`, by induction, with
`binom_succ'`).

## How it works

* The site is a static [Verso](https://github.com/leanprover/verso) document (Lean v4.34.0, the
  Verso of the IPM); `::::level (start := …) (target := …) (moves := …) (lean := …)` is a level
  (`ProbGame/Level.lean`), with `:::en` and `:::de` texts.
* `ProbGame/game.js` plays it in the browser: exact fractions, the moves as maps, the pushforward,
  the animation, the preimage of a tapped column, the Lean expression of the moves played, one
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
* `::::level`/`::::build` take `(no := "2.3") (proof := "(p : I) : …") (lemma := "…")`, and the texts
  of the proof are `:::proofen`/`:::proofde` (a paragraph that begins with *Tip.* is folded).
* `INVENTORY` in `game.js` lists the tactics, rules and lemmas with the level that introduces them;
  a line is refused before Lean sees it when it uses a tactic or theorem that is not in the inventory
  yet (or anything from Mathlib or the journal by its full name).
* `Lean/Solutions.lean` (and `Lean/Solutions0.lean` for world 0, whose context is
  `Lean/World0.lean`) holds a proof of every level as a player types it; `./check-proofs.sh`
  checks it with Lean, `python3 -I tests/proofs.py` plays it through the bridge.

## Lean as the referee

The game is built on the journal's `DiscreteMeasure` (`coin p` with `p : unitInterval`, its
complement `σ p`, `binom`, `LawfulMonad`). After each move the game asks Lean for the normal form of
the state: the moves played as a `DiscreteMeasure`, e.g. `((coin p).map not).map Bool.toNat`,
simplified with `#simp only [rules]`; the rules of world 1 are `Lean/World1.lean` and lemmas of
`DiscreteMeasure` (`coin_not'`, `map_pure`). The normal form is shown below the board
(`map Bool.toNat (coin (σ p))`), and a level is solved when the sand fills the target and Lean gives
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
```

## License

Apache 2.0, see `LICENSE`.
