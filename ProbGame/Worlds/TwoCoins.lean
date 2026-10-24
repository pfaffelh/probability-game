import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "World 2: Building with Coins" =>

%%%
htmlSplit := .never
%%%

:::en
Now you build. *New p-coin* lays down a coin; all coins have the same $`p` and are independent of
each other. Tap one or several cards and then a function: the result is a new card, with its
distribution, and functions apply to it again. A coin may go into several functions; then the
results depend on each other, and the game takes that into account. The distribution of a card is
found by going through all outcomes of the coins below it: with two coins, `true`–`true` has mass
$`p^2`, `true`–`false` $`p(1 - p)`, and so on.

*Check* compares the selected card (or else the newest) with the target, for every $`p`.
:::

:::de
Jetzt wird gebaut. *Neue p-Münze* legt eine Münze hin; alle Münzen haben dasselbe $`p` und sind
unabhängig voneinander. Tippe eine oder mehrere Karten an und dann eine Funktion: Das Ergebnis ist
eine neue Karte mit ihrer Verteilung, und auf sie lassen sich wieder Funktionen anwenden. Eine Münze
darf in mehrere Funktionen gehen; dann hängen die Ergebnisse voneinander ab, und das Spiel
berücksichtigt das. Die Verteilung einer Karte ergibt sich, indem man alle Ausgänge der Münzen unter
ihr durchgeht: Bei zwei Münzen hat `true`–`true` die Masse $`p^2`, `true`–`false` $`p(1 - p)`, und so weiter.

*Prüfen* vergleicht die ausgewählte Karte (sonst die neueste) mit dem Ziel, für jedes $`p`.
:::

::::build (target := "bool true:p^2 false:1-p^2") (moves := "not, and, or") (coins := "2")
:::en
*Both `true`.* Two coins, and `true` only when both show `true`.
:::

:::de
*Beide `true`.* Zwei Münzen, und `true` nur, wenn beide `true` zeigen.
:::
::::

::::build (target := "bool true:p(1-p) false:1-p(1-p)") (moves := "not, and, or") (coins := "2")
:::en
*First `true`, then `false`.*
:::

:::de
*Erst `true`, dann `false`.*
:::
::::

::::build (target := "bool true:2p-p^2 false:(1-p)^2") (moves := "not, and, or") (coins := "2")
:::en
*At least one `true`.* `false` only when both show `false`: $`(1 - p)^2`.
:::

:::de
*Mindestens einmal `true`.* `false` nur, wenn beide `false` zeigen: $`(1 - p)^2`.
:::
::::

::::build (target := "pure false") (moves := "not, and, or") (coins := "1")
:::en
*Surely `false`, with a single coin.* A coin that goes into two functions is the same coin in both:
the results depend on each other.
:::

:::de
*Sicher `false`, mit einer einzigen Münze.* Eine Münze, die in zwei Funktionen geht, ist in beiden
dieselbe: Die Ergebnisse hängen voneinander ab.
:::
::::

::::build (target := "bool true:2p(1-p) false:p^2+(1-p)^2") (moves := "not, and, or") (coins := "2")
:::en
*Exactly one `true`*, without a function for it: at least one, but not both.
:::

:::de
*Genau einmal `true`*, ohne eine Funktion dafür: mindestens einmal, aber nicht beide.
:::
::::

::::build (target := "nat 0:(1-p)^2 1:2p(1-p) 2:p^2") (moves := "not, and, or, toNat, add") (coins := "2")
:::en
*The number of `true`.* From coins to numbers ($`0` and $`1`), and add them: the binomial distribution $`B(2, p)`.
:::

:::de
*Die Anzahl `true`.* Von Münzen zu Zahlen ($`0` und $`1`), und addieren: die Binomialverteilung $`B(2, p)`.
:::
::::

::::build (target := "bool true:3p^2-2p^3 false:1-3p^2+2p^3") (moves := "not, and, or") (coins := "3")
:::en
*Boss: the majority of three.* `true` when at least two of three coins show `true`. Each coin has to
go into several functions.
:::

:::de
*Boss: die Mehrheit von dreien.* `true`, wenn mindestens zwei von drei Münzen `true` zeigen. Jede Münze
muss in mehrere Funktionen gehen.
:::
::::
