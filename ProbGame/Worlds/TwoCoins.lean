import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "World 2: Building with Coins" =>

%%%
htmlSplit := .never
%%%

:::en
Now you build a circuit. *New p-coin* lays down a coin, as a line; all coins have the same $`p` and
are independent of each other. Tap one or several lines and then a function: a column takes the
lines with a dot as its inputs, and its result runs on as a new line. A line that a column only
crosses, without a dot, is not used. A coin may go into several functions; then the results depend
on each other, and the game takes that into account. At the end of each line is its distribution,
found by going through all outcomes of the coins it comes from: with two coins, `true`–`true` has
mass $`p^2`, `true`–`false` $`p(1 - p)`, and so on. The circuit, read from left to right, is a
`do` block in Lean.

*Check* compares the selected line (or else the newest) with the target, for every $`p`.
:::

:::de
Jetzt baust du einen Schaltplan. *Neue p-Münze* legt eine Münze hin, als Leitung; alle Münzen haben
dasselbe $`p` und sind unabhängig voneinander. Tippe eine oder mehrere Leitungen an und dann eine
Funktion: Eine Spalte nimmt die Leitungen mit einem Punkt als Eingänge, und ihr Ergebnis läuft als
neue Leitung weiter. Eine Leitung, die eine Spalte nur kreuzt, ohne Punkt, wird nicht benutzt. Eine
Münze darf in mehrere Funktionen gehen; dann hängen die Ergebnisse voneinander ab, und das Spiel
berücksichtigt das. Am Ende jeder Leitung steht ihre Verteilung, die sich ergibt, indem man alle
Ausgänge der Münzen durchgeht, aus denen sie kommt: Bei zwei Münzen hat `true`–`true` die Masse
$`p^2`, `true`–`false` $`p(1 - p)`, und so weiter. Der Schaltplan, von links nach rechts gelesen, ist
ein `do`-Block in Lean.

*Prüfen* vergleicht die ausgewählte Leitung (sonst die neueste) mit dem Ziel, für jedes $`p`.
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
go into two functions.
:::

:::de
*Boss: die Mehrheit von dreien.* `true`, wenn mindestens zwei von drei Münzen `true` zeigen. Jede Münze
muss in zwei Funktionen gehen.
:::
::::
