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
found by going through all outcomes of the coins below it: with two coins, heads–heads has mass
$`p^2`, heads–tails $`p(1 - p)`, and so on.

*Check* compares the selected card (or else the newest) with the target, for every $`p`.
:::

:::de
Jetzt wird gebaut. *Neue p-Münze* legt eine Münze hin; alle Münzen haben dasselbe $`p` und sind
unabhängig voneinander. Tippe eine oder mehrere Karten an und dann eine Funktion: Das Ergebnis ist
eine neue Karte mit ihrer Verteilung, und auf sie lassen sich wieder Funktionen anwenden. Eine Münze
darf in mehrere Funktionen gehen; dann hängen die Ergebnisse voneinander ab, und das Spiel
berücksichtigt das. Die Verteilung einer Karte ergibt sich, indem man alle Ausgänge der Münzen unter
ihr durchgeht: Bei zwei Münzen hat Kopf–Kopf die Masse $`p^2`, Kopf–Zahl $`p(1 - p)`, und so weiter.

*Prüfen* vergleicht die ausgewählte Karte (sonst die neueste) mit dem Ziel, für jedes $`p`.
:::

::::build (target := "bool true:p^2 false:1-p^2") (moves := "not, and, or") (coins := "2")
:::en
*Both heads.* Two coins, and heads only when both show heads.
:::

:::de
*Beide Kopf.* Zwei Münzen, und Kopf nur, wenn beide Kopf zeigen.
:::
::::

::::build (target := "bool true:p(1-p) false:1-p(1-p)") (moves := "not, and, or") (coins := "2")
:::en
*First heads, then tails.*
:::

:::de
*Erst Kopf, dann Zahl.*
:::
::::

::::build (target := "bool true:2p-p^2 false:(1-p)^2") (moves := "not, and, or") (coins := "2")
:::en
*At least one heads.* Tails only when both show tails: $`(1 - p)^2`.
:::

:::de
*Mindestens einmal Kopf.* Zahl nur, wenn beide Zahl zeigen: $`(1 - p)^2`.
:::
::::

::::build (target := "pure false") (moves := "not, and, or") (coins := "1")
:::en
*Surely tails, with a single coin.* A coin that goes into two functions is the same coin in both:
the results depend on each other.
:::

:::de
*Sicher Zahl, mit einer einzigen Münze.* Eine Münze, die in zwei Funktionen geht, ist in beiden
dieselbe: Die Ergebnisse hängen voneinander ab.
:::
::::

::::build (target := "bool true:2p(1-p) false:p^2+(1-p)^2") (moves := "not, and, or") (coins := "2")
:::en
*Exactly one heads*, without a function for it: at least one, but not both.
:::

:::de
*Genau einmal Kopf*, ohne eine Funktion dafür: mindestens einmal, aber nicht beide.
:::
::::

::::build (target := "nat 0:(1-p)^2 1:2p(1-p) 2:p^2") (moves := "not, and, or, toNat, add") (coins := "2")
:::en
*The number of heads.* From coins to numbers, and add them: the binomial distribution $`B(2, p)`.
:::

:::de
*Die Anzahl Kopf.* Von Münzen zu Zahlen, und addieren: die Binomialverteilung $`B(2, p)`.
:::
::::

::::build (target := "bool true:3p^2-2p^3 false:1-3p^2+2p^3") (moves := "not, and, or") (coins := "3")
:::en
*Boss: the majority of three.* Heads when at least two of three coins show heads. Each coin has to
go into several functions.
:::

:::de
*Boss: die Mehrheit von dreien.* Kopf, wenn mindestens zwei von drei Münzen Kopf zeigen. Jede Münze
muss in mehrere Funktionen gehen.
:::
::::
