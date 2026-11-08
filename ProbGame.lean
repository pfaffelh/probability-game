import VersoManual
import ProbGame.Level
import ProbGame.Worlds.OneCoin
import ProbGame.Worlds.TwoCoins
import ProbGame.Worlds.Binomial

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
Distributions as sand. A distribution is drawn as columns of sand over the points of its space. A
*move* applies a map to it: the sand of each point flows to its image and piles up where several
points have the same image; the new distribution is the *image measure*. Every level has a *target*,
drawn as sand, and *building blocks*: a coin that shows `true` with probability $`p`, later the
binomial distribution. You *compose* them, with moves and with circuits of several coins, until the
sand has the shape of the target. The board checks it exactly, for every $`p` at once (the masses are
polynomials in $`p`); the slider only changes the picture. Your progress stays in your browser.

In [the full game](../main/), every level is then also proved in Lean.
:::

:::de
Verteilungen als Sand. Eine Verteilung ist als Säulen aus Sand über den Punkten ihres Raums
gezeichnet. Ein *Zug* wendet eine Abbildung auf sie an: Der Sand jedes Punkts fließt zu seinem Bild
und häuft sich dort, wo mehrere Punkte dasselbe Bild haben; die neue Verteilung ist das *Bildmaß*.
Jedes Level hat ein *Ziel*, als Sand gezeichnet, und *Bausteine*: eine Münze, die mit
Wahrscheinlichkeit $`p` `true` zeigt, später die Binomialverteilung. Du *setzt* sie *zusammen*, mit
Zügen und mit Schaltplänen aus mehreren Münzen, bis der Sand die Form des Ziels hat. Das Spielfeld
prüft das exakt, für jedes $`p` zugleich (die Massen sind Polynome in $`p`); der Schieberegler ändert
nur das Bild. Dein Fortschritt bleibt in deinem Browser.

Im [ganzen Spiel](../main/) wird jedes Level danach auch in Lean bewiesen.
:::

{include 1 ProbGame.Worlds.OneCoin}

{include 1 ProbGame.Worlds.TwoCoins}

{include 1 ProbGame.Worlds.Binomial}
