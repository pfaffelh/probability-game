import VersoManual
import ProbGame.Level
import ProbGame.Worlds.Walk
import ProbGame.Worlds.OneCoin
import ProbGame.Worlds.TwoCoins
import ProbGame.Worlds.Binomial

open Verso.Genre Manual
open ProbGame

#doc (Manual) "The Probability Game" =>

%%%
authors := ["Peter Pfaffelhuber"]
%%%

:::en
Distributions as sand: a distribution is drawn as columns of sand over the points of its space, and a
*move* applies a map to it. The sand flows to the images; the new distribution is the *image measure*
(pushforward). Every level has two parts, as in the Natural Number Game: first you find the statement
on the board, then you prove it in Lean, for every probability $`p`, with the tactics and theorems of
your inventory. Each lemma you prove is unlocked for the levels after it. Lean runs on the server;
your progress stays in your browser.
The first world comes before chance: a figure walks on a grid, with moves that are sure or that go
several ways at once; there the same monad laws are at work as later for distributions.
:::

:::de
Verteilungen als Sand: Eine Verteilung ist als Säulen aus Sand über den Punkten ihres Raums gezeichnet,
und ein *Zug* wendet eine Abbildung auf sie an. Der Sand fließt zu den Bildern; die neue Verteilung ist
das *Bildmaß*. Jedes Level hat zwei Teile, wie im Natural Number Game: Zuerst findest du die Aussage
auf dem Spielfeld, dann beweist du sie in Lean, für jede Wahrscheinlichkeit $`p`, mit den Taktiken und
Sätzen deines Inventars. Jedes Lemma, das du beweist, wird für die Level danach freigeschaltet. Lean
läuft auf dem Server; dein Fortschritt bleibt in deinem Browser.
Die erste Welt kommt vor dem Zufall: Eine Figur geht auf einem Gitter, mit Zügen, die sicher sind oder
in mehrere Richtungen zugleich gehen; dort wirken schon dieselben Monadengesetze wie später für
Verteilungen.
:::

{include 1 ProbGame.Worlds.Walk}

{include 1 ProbGame.Worlds.OneCoin}

{include 1 ProbGame.Worlds.TwoCoins}

{include 1 ProbGame.Worlds.Binomial}
