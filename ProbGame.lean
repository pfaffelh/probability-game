import VersoManual
import ProbGame.Level
import ProbGame.Worlds.OneCoin
import ProbGame.Worlds.TwoCoins
import ProbGame.Worlds.Binomial
import ProbGame.Lexicon

open Verso.Genre Manual
open ProbGame

/-! This file is the edition of the game: its worlds and its front page. It is the file in which the
branches differ (see `BRANCHES.md`): `main` (the worlds of chance, with proofs), `monad` (with the
grid and its monads), `show` (the boards alone, without proofs). -/

/-- The edition: `"show"` plays the boards alone, without Lean and without proofs (see `game.js`). -/
def ProbGame.edition : String := "show"

#doc (Manual) "The Probability Game" =>

%%%
authors := ["Peter Pfaffelhuber"]
%%%

:::en
A distribution, in mathematics also called a probability measure, is drawn as a bar chart: over each
point of its space a bar, as high as the point's mass. A *move* applies a map to it: the mass of each
point goes to its image, and where several points have the same image, their masses add up; the new
distribution is the *image measure*. Every level has a *target*, a distribution too, and *building
blocks*: a coin that shows `true` with probability $`p`, later the binomial distribution. You
*compose* them, with moves and with circuits of several coins, until the distribution has the shape of
the target. The board checks it exactly, for every $`p` at once (the masses are polynomials in $`p`);
the slider only changes the picture. Your progress stays in your browser.

In [the full game](../main/), every level is then also proved in Lean.
:::

{include 1 ProbGame.Worlds.OneCoin}

{include 1 ProbGame.Worlds.TwoCoins}

{include 1 ProbGame.Worlds.Binomial}

{include 1 ProbGame.Lexicon}
