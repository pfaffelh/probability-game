import VersoManual
import ProbGame.Level
import ProbGame.Worlds.OneCoin

open Verso.Genre Manual
open ProbGame

#doc (Manual) "The Probability Game" =>

%%%
authors := ["Peter Pfaffelhuber"]
%%%

:::en
Distributions as sand: a distribution is drawn as columns of sand over the points of its space, and a
*move* applies a map to it. The sand flows to the images; the new distribution is the *image measure*
(pushforward). Every level is a statement about distributions that is proved in Lean, with Mathlib's
`PMF`, for every probability $`p`.
:::

:::de
Verteilungen als Sand: Eine Verteilung ist als Säulen aus Sand über den Punkten ihres Raums gezeichnet,
und ein *Zug* wendet eine Abbildung auf sie an. Der Sand fließt zu den Bildern; die neue Verteilung ist
das *Bildmaß*. Jedes Level ist eine Aussage über Verteilungen, die in Lean bewiesen ist, mit Mathlibs
`PMF`, für jede Wahrscheinlichkeit $`p`.
:::

{include 1 ProbGame.Worlds.OneCoin}
