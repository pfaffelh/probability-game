# The Probability Game

Distributions as sand. A distribution is drawn as columns of sand over the points of its space; a
*move* applies a map to it, the sand of each point flows to its image (animated), and where several
points have the same image it piles up. The new distribution is the *image measure* (pushforward)
$P \circ f^{-1}$. Tapping a column shows its preimage. A level is solved when the sand fills the
dashed target; then its Lean statement is shown, which holds for every probability $p$ and is proved
with Mathlib's `PMF`.

**World 1, one coin** (Bernoulli(1/3) at the start): flip; always heads (a point mass); surely tails
without "always tails" (a composition); heads = 1, tails = 0 (to ℕ); the order matters; a bet
(+5 / −2, to ℤ); the better bet; surely zero.

## How it works

* The site is a static [Verso](https://github.com/leanprover/verso) document (Lean v4.34.0, the
  Verso of the IPM); `::::level (start := …) (target := …) (moves := …) (lean := …)` is a level
  (`ProbGame/Level.lean`), with `:::en` and `:::de` texts.
* `ProbGame/game.js` plays it in the browser: exact fractions, the moves as maps, the pushforward,
  the animation, the preimage of a tapped column, the Lean expression of the moves played, one
  level at a time with a dot per level, progress in the browser, English or German.
* The Lean statements of the levels are in `Proofs/` and checked against Mathlib with
  `./check-proofs.sh [project with Mathlib]` (default `~/Code/lean/journal`; also checked with
  nng4's Mathlib). The game needs no Lean while it is played.
* In Mathlib v4.34, `PMF.bernoulli` is deprecated in favour of `ProbabilityTheory.bernoulliMeasure`;
  the proofs still use `PMF` (they work with both versions).

## Lean as the referee

The game is built on the journal's `DiscreteMeasure` (`coin p` with `p : unitInterval`, its
complement `σ p`, `binom`, `LawfulMonad`). After each move the game asks Lean for the normal form of
the state: the moves played as a `DiscreteMeasure`, e.g. `((coin p).map not).map Bool.toNat`,
simplified with `#simp only [rules]`; the rules of world 1 are `Lean/World1.lean` and lemmas of
`DiscreteMeasure` (`coin_not'`, `map_pure`). The normal form is shown below the board
(`map Bool.toNat (coin (σ p))`), and a level is solved when the sand fills the target and Lean gives
the state and the target the same normal form, so that it holds for every `p`. Different correct
ways to the target lead to the same normal form; a wrong one does not.

Lean runs in the bridge of nng-verso (`repl/bridge.py`, `/simp`), on the Lean REPL, with
`DiscreteMeasure` as its base:

```bash
cd ~/Code/lean/journal && BASE="import Journal.Notes.DiscreteMeasure.Thinning" \
  REPL=~/Code/lean/repl-v4.34/.lake/build/bin/repl python3 -I ~/Code/lean/verso_game/repl/bridge.py 8091
# then the site with ?backend=http://127.0.0.1:8091
```

Without the bridge the sand still plays, for the example `p = 1/3`, with a note that Lean is not
connected. (The REPL with all of Mathlib loaded needs about 7 GB; `DiscreteMeasure` imports all of
Mathlib, and importing only what it needs would make that much smaller.)

## Building

```bash
lake build && lake exe probgame          # writes the site to _out/html-multi
cd _out/html-multi && python3 -m http.server 8004
./check-proofs.sh                        # the Lean statements of the levels, and the rules
```
