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

## Building

```bash
lake build && lake exe probgame          # writes the site to _out/html-multi
cd _out/html-multi && python3 -m http.server 8004
./check-proofs.sh                        # the Lean statements of the levels
```
