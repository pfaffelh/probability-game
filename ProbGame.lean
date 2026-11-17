import VersoManual
import ProbGame.Level
import ProbGame.Worlds.Masses
import ProbGame.Worlds.OneCoin
import ProbGame.Worlds.Maps
import ProbGame.Worlds.TwoCoins
import ProbGame.Worlds.Counting
import ProbGame.Worlds.Circuits
import ProbGame.Worlds.Bind
import ProbGame.Worlds.RealNumbers
import ProbGame.Worlds.Thinning
import ProbGame.Worlds.Sequences
import ProbGame.Worlds.Binomial
import ProbGame.Worlds.Geometric
import ProbGame.Worlds.Hypergeometric
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
*Goal.* Here you learn some basics of probability theory, but the main part is their
implementation in Lean: every statement you find on the board, you then prove in Lean.
:::

:::de
*Ziel.* Hier lernst du einige Grundlagen der Wahrscheinlichkeitstheorie, aber der Hauptteil ist
ihre Umsetzung in Lean: Jede Aussage, die du auf dem Spielfeld findest, beweist du danach in Lean.
:::

:::en
*Prerequisites.* Having taken a course in probability theory is not required. A first contact with
Lean is useful, but not necessary.
:::

:::de
*Voraussetzungen.* Eine Vorlesung über Wahrscheinlichkeitstheorie ist nicht nötig. Ein erster
Kontakt mit Lean ist nützlich, aber keine Voraussetzung.
:::

:::en
*Probability keywords.* Coin toss, distribution (probability measure), image measure
(pushforward), independence, two-stage experiments, counting, sequences of coins, binomial
distribution, geometric distribution, thinning, hypergeometric distribution.
:::

:::de
*Stichworte Wahrscheinlichkeit.* Münzwurf, Verteilung (Wahrscheinlichkeitsmaß), Bildmaß,
Unabhängigkeit, zweistufige Experimente, Zählen, Folgen von Münzen, Binomialverteilung,
geometrische Verteilung, Ausdünnen, hypergeometrische Verteilung.
:::

:::picture (kind := "coin move binom geom")
:::

:::en
*Lean keywords.* Goal and tactic; rewriting with `rw`; `rfl`, `exact`, `apply`; case analysis with
`cases` and `decide`; induction; computing with `norm_num`, `ring` and `linear_combination`;
`congr` and `funext`; the types `Bool`, `ℕ`, `ℝ` and `ℝ≥0∞`; `do` notation and monads (`pure`,
bind); theorems of Mathlib.
:::

:::de
*Stichworte Lean.* Ziel und Taktik; Umschreiben mit `rw`; `rfl`, `exact`, `apply`;
Fallunterscheidung mit `cases` und `decide`; Induktion; Rechnen mit `norm_num`, `ring` und
`linear_combination`; `congr` und `funext`; die Typen `Bool`, `ℕ`, `ℝ` und `ℝ≥0∞`; `do`-Notation
und Monaden (`pure`, bind); Sätze aus Mathlib.
:::

:::picture (kind := "lean")
:::

:::en
*How to play.* A distribution is drawn as a bar chart: over each point of its space a bar, as high
as the point's mass. A *move* applies a map to it; the mass of each point goes to its image, and
the new distribution is the *image measure*. Every level has two parts, as in the Natural Number
Game: first you find the statement on the board, then you prove it in Lean, for every probability
$`p`, with the tactics and theorems of your inventory. Each lemma you prove is unlocked for the
levels after it. Lean runs on the server; your progress stays in your browser.
:::

:::de
*So wird gespielt.* Eine Verteilung ist als Säulendiagramm gezeichnet: über jedem Punkt ihres
Raums eine Säule, so hoch wie seine Masse. Ein *Zug* wendet eine Abbildung auf sie an; die Masse
jedes Punkts geht zu seinem Bild, und die neue Verteilung ist das *Bildmaß*. Jedes Level hat zwei
Teile, wie im Natural Number Game: Zuerst findest du die Aussage auf dem Spielfeld, dann beweist du
sie in Lean, für jede Wahrscheinlichkeit $`p`, mit den Taktiken und Sätzen deines Inventars. Jedes
Lemma, das du beweist, wird für die Level danach freigeschaltet. Lean läuft auf dem Server; dein
Fortschritt bleibt in deinem Browser.
:::

:::en
*The worlds.* One world comes before chance: circuits of `true` and `false`; then how Lean writes a
distribution. Then a coin with probability $`p`, what it is and where its mass goes; the maps
`Bool → Bool`, on values and on coins; circuits of coins, read as `do` blocks, and counting; coins
that wait for others (bind); sequences of coins; the binomial formula by induction; the geometric
distribution; thinning, of a coin, a geometric and a binomial distribution; the hypergeometric
distribution. The board leads at first; Lean grows from world to world.
:::

:::de
*Die Welten.* Eine Welt kommt vor dem Zufall: Schaltungen aus `true` und `false`; dann, wie Lean
eine Verteilung schreibt. Dann eine Münze mit Wahrscheinlichkeit $`p`, was sie ist und wohin ihre
Masse geht; die Abbildungen `Bool → Bool`, auf Werten und auf Münzen; Schaltungen aus Münzen,
gelesen als `do`-Blöcke, und Zählen; Münzen, die auf andere warten (bind); Folgen von Münzen; die
Binomialformel durch Induktion; die geometrische Verteilung; Ausdünnen, einer Münze, einer
geometrischen und einer Binomialverteilung; die hypergeometrische Verteilung. Am Anfang führt das
Spielfeld; Lean wächst von Welt zu Welt.
:::

{include 1 ProbGame.Worlds.Circuits}

{include 1 ProbGame.Worlds.Masses}

{include 1 ProbGame.Worlds.OneCoin}

{include 1 ProbGame.Worlds.Maps}

{include 1 ProbGame.Worlds.TwoCoins}

{include 1 ProbGame.Worlds.Counting}

{include 1 ProbGame.Worlds.Bind}

{include 1 ProbGame.Worlds.RealNumbers}

{include 1 ProbGame.Worlds.Sequences}

{include 1 ProbGame.Worlds.Binomial}

{include 1 ProbGame.Worlds.Geometric}

{include 1 ProbGame.Worlds.Thinning}

{include 1 ProbGame.Worlds.Hypergeometric}

{include 1 ProbGame.Lexicon}
