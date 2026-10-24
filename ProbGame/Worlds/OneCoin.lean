import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "World 1: One Coin" =>

%%%
htmlSplit := .never
%%%

:::en
A coin shows *heads* with probability $`p` and *tails* with probability $`1 - p`, for any $`p`. Its
distribution is drawn as two columns of sand. A *move* applies a map $`f` to the outcome: the sand
of each outcome flows to its image, and where several outcomes have the same image, their sand piles
up. What you get is the distribution of $`f(X)`, the *image measure* $`P \circ f^{-1}`:
$`P(f(X) = b) = P(X \in f^{-1}(\{b\}))`. Tap a column to see where its sand came from.

Bring the sand into the shape of the target, drawn on the right (and dashed on the board when it
lives on the same space). The masses are $`p` and $`1 - p`; the picture shows them for an example
$`p`, which the slider changes.
:::

:::de
Eine Münze zeigt *Kopf* mit Wahrscheinlichkeit $`p` und *Zahl* mit Wahrscheinlichkeit $`1 - p`, für
ein beliebiges $`p`. Ihre Verteilung ist als zwei Säulen aus Sand gezeichnet. Ein *Zug* wendet eine
Abbildung $`f` auf das Ergebnis an: Der Sand jedes Ergebnisses fließt zu seinem Bild, und wo mehrere
Ergebnisse dasselbe Bild haben, häuft er sich. Was herauskommt, ist die Verteilung von $`f(X)`, das
*Bildmaß* $`P \circ f^{-1}`: $`P(f(X) = b) = P(X \in f^{-1}(\{b\}))`. Tippe eine Säule an, um zu
sehen, woher ihr Sand kommt.

Bring den Sand in die Form des Ziels, das rechts gezeichnet ist (und gestrichelt auf dem Spielfeld,
wenn es auf demselben Raum lebt). Die Massen sind $`p` und $`1 - p`; das Bild zeigt sie für ein
Beispiel-$`p`, das der Schieberegler ändert.
:::

::::level (start := "bernoulli p") (target := "bernoulli 1-p") (moves := "not") (lean := "(bernoulli p h).map not = bernoulli (1 - p) tsub_le_self") (leanTarget := "coin (σ p)")
:::en
*Flip the coin.* Heads becomes tails and tails heads: the two columns swap.
:::

:::de
*Dreh die Münze um.* Aus Kopf wird Zahl und aus Zahl Kopf: Die beiden Säulen tauschen.
:::
::::

::::level (start := "bernoulli p") (target := "pure true") (moves := "not, heads, tails") (lean := "(bernoulli p h).map (fun _ => true) = pure true") (leanTarget := "DiscreteMeasure.pure true")
:::en
*Always heads.* A constant map sends both outcomes to the same point: all the sand flows together.
The result is sure, a point mass (Dirac measure).
:::

:::de
*Immer Kopf.* Eine konstante Abbildung schickt beide Ergebnisse auf denselben Punkt: Der ganze Sand
fließt zusammen. Das Ergebnis ist sicher, eine Punktmasse (Dirac-Maß).
:::
::::

::::level (start := "bernoulli p") (target := "pure false") (moves := "not, heads") (lean := "((bernoulli p h).map (fun _ => true)).map not = pure false") (leanTarget := "DiscreteMeasure.pure false")
:::en
*Surely tails, but there is no “always tails”.* Two moves one after the other: the image measure of
the image measure is the image measure of the composition, $`(P \circ f^{-1}) \circ g^{-1} = P \circ (g \circ f)^{-1}`.
:::

:::de
*Sicher Zahl, aber es gibt kein „immer Zahl“.* Zwei Züge nacheinander: Das Bildmaß des Bildmaßes ist
das Bildmaß der Verkettung, $`(P \circ f^{-1}) \circ g^{-1} = P \circ (g \circ f)^{-1}`.
:::
::::

::::level (start := "bernoulli p") (target := "nat 1:p 0:1-p") (moves := "not, toNat") (lean := "(bernoulli p h).map Bool.toNat 1 = p") (leanTarget := "map Bool.toNat (coin p)")
:::en
*From sides to numbers.* Count heads as $`1` and tails as $`0`: the distribution moves to the natural
numbers. This is how a coin becomes a random number.
:::

:::de
*Von Seiten zu Zahlen.* Zähle Kopf als $`1` und Zahl als $`0`: Die Verteilung wandert zu den
natürlichen Zahlen. So wird aus einer Münze eine Zufallszahl.
:::
::::

::::level (start := "bernoulli p") (target := "nat 1:1-p 0:p") (moves := "not, toNat") (lean := "((bernoulli p h).map not).map Bool.toNat 1 = 1 - p") (leanTarget := "map Bool.toNat (coin (σ p))")
:::en
*The order matters.* Once the coin has become a number, it cannot be flipped any more.
:::

:::de
*Die Reihenfolge zählt.* Ist die Münze erst eine Zahl, lässt sie sich nicht mehr umdrehen.
:::
::::

::::level (start := "bernoulli p") (target := "int 5:p -2:1-p") (moves := "not, toNat, payoff 5 -2") (lean := "(bernoulli p h).map (fun b => if b then (5 : ℤ) else -2) 5 = p") (leanTarget := "map (fun b => if b = true then (5 : ℤ) else -2) (coin p)")
:::en
*A bet.* Heads wins 5 euros, tails loses 2. The image measure is the distribution of your gain.
:::

:::de
*Eine Wette.* Bei Kopf gewinnst du 5 Euro, bei Zahl verlierst du 2. Das Bildmaß ist die Verteilung
deines Gewinns.
:::
::::

::::level (start := "bernoulli p") (target := "int 5:1-p -2:p") (moves := "not, toNat, payoff 5 -2") (lean := "((bernoulli p h).map not).map (fun b => if b then (5 : ℤ) else -2) 5 = 1 - p") (leanTarget := "map (fun b => if b = true then (5 : ℤ) else -2) (coin (σ p))")
:::en
*A better bet.* Make winning the likely outcome.
:::

:::de
*Eine bessere Wette.* Mach den Gewinn zum wahrscheinlichen Ausgang.
:::
::::

::::level (start := "bernoulli p") (target := "nat 0:1") (moves := "not, heads, tails, toNat") (lean := "((bernoulli p h).map (fun _ => false)).map Bool.toNat = pure 0") (leanTarget := "DiscreteMeasure.pure 0")
:::en
*Surely zero.* A point mass on the numbers, however you get there.
:::

:::de
*Sicher null.* Eine Punktmasse auf den Zahlen, egal auf welchem Weg.
:::
::::
