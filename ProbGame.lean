import VersoManual
import ProbGame.Level
import ProbGame.Worlds.OneCoin
import ProbGame.Worlds.Draw
import ProbGame.Worlds.TwoCoins
import ProbGame.Worlds.Circuits
import ProbGame.Worlds.Bind
import ProbGame.Lexicon

open Verso.Genre Manual
open ProbGame

/-! This file is the edition of the game: its worlds and its front page. It is the file in which the
branches differ (see `BRANCHES.md`): `main` (the worlds of chance, with proofs), `monad` (with the
grid and its monads), `show` (the boards alone, without proofs). -/

/-- The edition: `"show"` plays the boards alone, without Lean and without proofs (see `game.js`). -/
def ProbGame.edition : String := "main"

#doc (Manual) "The Probability Game" =>

%%%
authors := ["Peter Pfaffelhuber"]
%%%

:::en
A distribution, in mathematics also called a probability measure, is drawn as a bar chart: over each
point of its space a bar, as high as the point's mass. A *move* applies a map to it. The mass of each
point goes to its image; the new distribution is the *image measure* (pushforward). Every level has two parts, as in the Natural Number Game: first you find the statement
on the board, then you prove it in Lean, for every probability $`p`, with the tactics and theorems of
your inventory. Each lemma you prove is unlocked for the levels after it. Lean runs on the server;
your progress stays in your browser.
One world comes before chance: circuits of `true` and `false`, and the maps `Bool → Bool`. Then a coin with probability $`p`, what it is and where its mass
goes; drawing and computing in `do` blocks; circuits of coins and counting; and coins that wait for
others (bind). The board leads at first; Lean grows from world to world.
:::

:::de
Eine Verteilung, in der Mathematik auch Wahrscheinlichkeitsmaß genannt, ist als Säulendiagramm
gezeichnet: über jedem Punkt ihres Raums eine Säule, so hoch wie seine Masse. Ein *Zug* wendet eine
Abbildung auf sie an. Die Masse jedes Punkts geht zu seinem Bild; die neue Verteilung ist das *Bildmaß*. Jedes Level hat zwei Teile, wie im Natural Number Game: Zuerst findest du die Aussage
auf dem Spielfeld, dann beweist du sie in Lean, für jede Wahrscheinlichkeit $`p`, mit den Taktiken und
Sätzen deines Inventars. Jedes Lemma, das du beweist, wird für die Level danach freigeschaltet. Lean
läuft auf dem Server; dein Fortschritt bleibt in deinem Browser.
Eine Welt kommt vor dem Zufall: Schaltungen aus `true` und `false`, und die Abbildungen `Bool → Bool`.
Dann eine Münze mit Wahrscheinlichkeit $`p`, was
sie ist und wohin ihre Masse geht; Ziehen und Rechnen in `do`-Blöcken; Schaltungen aus Münzen und
Zählen; und Münzen, die auf andere warten (bind). Am Anfang führt das Spielfeld; Lean wächst von Welt zu
Welt.
:::

{include 1 ProbGame.Worlds.Circuits}

{include 1 ProbGame.Worlds.OneCoin}

{include 1 ProbGame.Worlds.Draw}

{include 1 ProbGame.Worlds.TwoCoins}

{include 1 ProbGame.Worlds.Bind}

{include 1 ProbGame.Lexicon}
