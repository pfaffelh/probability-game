import VersoManual
import ProbGame.Level
import ProbGame.Worlds.ENNReal
import ProbGame.Worlds.Masses
import ProbGame.Worlds.OneCoin
import ProbGame.Worlds.TwoCoins
import ProbGame.Worlds.DoLaws
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
*Probability keywords.* Coin toss, distribution, image measure, independence, two-stage experiment,
counting, binomial distribution, geometric distribution, thinning, hypergeometric distribution.
:::

:::de
*Stichworte Wahrscheinlichkeit.* Münzwurf, Verteilung, Bildmaß, Unabhängigkeit, zweistufiges
Experiment, Zählen, Binomialverteilung, geometrische Verteilung, Ausdünnen, hypergeometrische
Verteilung.
:::

:::en
*Lean keywords.* Goal, tactic, `rfl`, `rw`, `exact`, `apply`, `cases`, `decide`, induction,
`simp`, `ring`, `field_simp`, `linear_combination`, `congr`, `funext`, `Bool`, `ℕ`, `ℝ`, `ℝ≥0∞`, `do`
notation, monad, Mathlib.
:::

:::de
*Stichworte Lean.* Ziel, Taktik, `rfl`, `rw`, `exact`, `apply`, `cases`, `decide`, Induktion,
`simp`, `ring`, `field_simp`, `linear_combination`, `congr`, `funext`, `Bool`, `ℕ`, `ℝ`, `ℝ≥0∞`,
`do`-Notation, Monade, Mathlib.
:::

{include 1 ProbGame.Worlds.Circuits}

{include 1 ProbGame.Worlds.ENNReal}

{include 1 ProbGame.Worlds.Masses}

{include 1 ProbGame.Worlds.OneCoin}

{include 1 ProbGame.Worlds.TwoCoins}

{include 1 ProbGame.Worlds.DoLaws}

{include 1 ProbGame.Worlds.Counting}

{include 1 ProbGame.Worlds.Bind}

{include 1 ProbGame.Worlds.RealNumbers}

{include 1 ProbGame.Worlds.Sequences}

{include 1 ProbGame.Worlds.Binomial}

{include 1 ProbGame.Worlds.Geometric}

{include 1 ProbGame.Worlds.Thinning}

{include 1 ProbGame.Worlds.Hypergeometric}

{include 1 ProbGame.Lexicon}
