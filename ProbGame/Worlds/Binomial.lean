import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "World 3: Counting" =>

%%%
htmlSplit := .never
%%%

:::en
Throw $`n` coins and count how often `true` comes up: that is the *binomial distribution*
$`B(n, p)`, with $`P(k) = \binom{n}{k} p^k (1 - p)^{n - k}`. In Lean it is `binom p n`. In world 2
you built $`B(2, p)` from two coins; from the third level on it is a building block of its own.
:::

:::de
Wirf $`n` Münzen und zähle, wie oft `true` kommt: Das ist die *Binomialverteilung* $`B(n, p)`, mit
$`P(k) = \binom{n}{k} p^k (1 - p)^{n - k}`. In Lean heißt sie `binom p n`. In Welt 2 hast du
$`B(2, p)` aus zwei Münzen gebaut; ab dem dritten Level ist sie ein eigener Baustein.
:::

::::build (target := "nat 0:(1-p)^3 1:3p(1-p)^2 2:3p^2(1-p) 3:p^3") (moves := "toNat, add") (coins := "3")
:::en
*Three coins.* Count the `true`s among three coins.
:::

:::de
*Drei Münzen.* Zähle die `true` unter drei Münzen.
:::
::::

::::build (target := "nat 0:(1-p)^4 1:4p(1-p)^3 2:6p^2(1-p)^2 3:4p^3(1-p) 4:p^4") (moves := "toNat, add, count") (coins := "4")
:::en
*Four coins, in one go.* The new function counts the `true`s on as many lines as you choose.
:::

:::de
*Vier Münzen, in einem Zug.* Die neue Funktion zählt die `true` auf so vielen Leitungen, wie du
auswählst.
:::
::::

::::build (target := "nat 0:(1-p)^3 1:3p(1-p)^2 2:3p^2(1-p) 3:p^3") (moves := "toNat, add") (sources := "coin:1, binom2:1")
:::en
*A new building block.* $`B(2, p)` and one more coin give $`B(3, p)`: one more throw, one more
chance to count.
:::

:::de
*Ein neuer Baustein.* $`B(2, p)` und eine weitere Münze ergeben $`B(3, p)`: ein Wurf mehr, eine
Chance mehr zu zählen.
:::
::::

::::build (target := "bool true:2p-p^2 false:(1-p)^2") (moves := "toNat, add, pos") (sources := "binom2:1")
:::en
*At least one `true`*, as in world 2, but this time from $`B(2, p)`: when is a number at least $`1`?
:::

:::de
*Mindestens einmal `true`*, wie in Welt 2, aber diesmal aus $`B(2, p)`: Wann ist eine Zahl mindestens
$`1`?
:::
::::

::::build (target := "nat 0:(1-p)^4 1:4p(1-p)^3 2:6p^2(1-p)^2 3:4p^3(1-p) 4:p^4") (moves := "add, max") (sources := "binom2:2")
:::en
*Boss: $`B(2, p) * B(2, p) = B(4, p)`.* Two independent binomials, no coins. The sum of independent
random numbers has the *convolution* $`*` of their distributions as its distribution. In Lean,
`(do let X ← binom p 2; let Y ← binom p 2; return X + Y) = binom p 4`, for every $`p`: a case of
the lemma `binom_add`.
:::

:::de
*Endgegner: $`B(2, p) * B(2, p) = B(4, p)`.* Zwei unabhängige Binomialverteilungen, keine Münzen. Die
Summe unabhängiger Zufallszahlen hat die *Faltung* $`*` ihrer Verteilungen als Verteilung. In Lean:
`(do let X ← binom p 2; let Y ← binom p 2; return X + Y) = binom p 4`, für jedes $`p`, ein Fall des
Lemmas `binom_add`.
:::
::::
