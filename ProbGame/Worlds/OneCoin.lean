import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "World 1: One Coin" =>

%%%
htmlSplit := .never
%%%

:::en
A coin shows `true` with probability $`p` and `false` with probability $`1 - p`, for any $`p`, as in
Lean, where a coin is a random `Bool`. Its
distribution is drawn as two columns of sand. A *move* applies a map $`f` to the outcome: the sand
of each outcome flows to its image, and where several outcomes have the same image, their sand piles
up. What you get is the distribution of $`f(X)`, the *image measure* $`P \circ f^{-1}`:
$`P(f(X) = b) = P(X \in f^{-1}(\{b\}))`. Tap a column to see where its sand came from.

Bring the sand into the shape of the target, drawn on the right (and dashed on the board when it
lives on the same space). The masses are $`p` and $`1 - p`; the picture shows them for an example
$`p`, which the slider changes.
:::

:::de
Eine Münze zeigt `true` mit Wahrscheinlichkeit $`p` und `false` mit Wahrscheinlichkeit $`1 - p`, für
ein beliebiges $`p`, wie in Lean, wo eine Münze ein zufälliges `Bool` ist. Ihre Verteilung ist als zwei Säulen aus Sand gezeichnet. Ein *Zug* wendet eine
Abbildung $`f` auf das Ergebnis an: Der Sand jedes Ergebnisses fließt zu seinem Bild, und wo mehrere
Ergebnisse dasselbe Bild haben, häuft er sich. Was herauskommt, ist die Verteilung von $`f(X)`, das
*Bildmaß* $`P \circ f^{-1}`: $`P(f(X) = b) = P(X \in f^{-1}(\{b\}))`. Tippe eine Säule an, um zu
sehen, woher ihr Sand kommt.

Bring den Sand in die Form des Ziels, das rechts gezeichnet ist (und gestrichelt auf dem Spielfeld,
wenn es auf demselben Raum lebt). Die Massen sind $`p` und $`1 - p`; das Bild zeigt sie für ein
Beispiel-$`p`, das der Schieberegler ändert.
:::

::::level (start := "bernoulli p") (target := "bernoulli 1-p") (moves := "not") (lean := "(bernoulli p h).map not = bernoulli (1 - p) tsub_le_self") (leanTarget := "coin (σ p)") (no := "1.1") (proof := "(p : I) : not <$> coin p = coin (σ p)")
:::en
*Flip the coin.* `not` makes `true` into `false` and `false` into `true`: the two columns swap.
:::

:::de
*Dreh die Münze um.* `not` macht aus `true` `false` und aus `false` `true`: Die beiden Säulen tauschen.
:::

:::proofen
*Now the proof.* What the board showed, now in Lean, for every $`p`. In Lean the coin is `coin p`,
and `f <$> μ` is the image measure of `μ` under `f`: the move `f` applied to the distribution `μ`;
`σ p` is $`1 - p`, and `p : I` says that $`p` lies in the unit interval $`I = [0, 1]`. Below is the
*goal*, what is to be shown.

The first rule of the game is `coin_not : not <$> coin p = coin (σ p)`: flipping swaps the masses.
The tactic `rw [coin_not]` *rewrites* the goal with it: it replaces the left side of the rule by its
right side. When both sides of the goal are then the same, the goal is closed. Type it (or tap
`coin_not` in the inventory) and press *Run*.
:::

:::proofde
*Jetzt der Beweis.* Was das Spielfeld gezeigt hat, jetzt in Lean, für jedes $`p`. In Lean ist die
Münze `coin p`, und `f <$> μ` ist das Bildmaß von `μ` unter `f`: der Zug `f`, angewandt auf die
Verteilung `μ`; `σ p` ist $`1 - p`, und `p : I` sagt, dass $`p` im Einheitsintervall $`I = [0, 1]` liegt. Unten
steht das *Ziel*, also das, was zu zeigen ist.

Die erste Regel des Spiels ist `coin_not : not <$> coin p = coin (σ p)`: Umdrehen tauscht die
Massen. Die Taktik `rw [coin_not]` *schreibt* das Ziel damit *um*: Sie ersetzt die linke Seite der
Regel durch ihre rechte. Sind danach beide Seiten des Ziels gleich, ist das Ziel erledigt. Tippe sie
ein (oder tippe `coin_not` im Inventar an) und drücke *Ausführen*.
:::
::::

::::level (start := "bernoulli p") (target := "pure true") (moves := "not, heads, tails") (lean := "(bernoulli p h).map (fun _ => true) = pure true") (leanTarget := "DiscreteMeasure.pure true") (no := "1.2") (proof := "(p : I) : (fun _ => true) <$> coin p = pure true")
:::en
*Always `true`.* A constant map sends both outcomes to the same point: all the sand flows together.
The result is sure, a point mass (Dirac measure).
:::

:::de
*Immer `true`.* Eine konstante Abbildung schickt beide Ergebnisse auf denselben Punkt: Der ganze Sand
fließt zusammen. Das Ergebnis ist sicher, eine Punktmasse (Dirac-Maß).
:::

:::proofen
`pure b` is the point mass at `b`, and `fun _ => true` is the constant map. The new rule
`coin_const : (fun _ => b) <$> coin p = pure b` says what the board showed: all the sand flows to
one point.
:::

:::proofde
`pure b` ist die Punktmasse in `b`, und `fun _ => true` ist die konstante Abbildung. Die neue
Regel `coin_const : (fun _ => b) <$> coin p = pure b` sagt, was das Spielfeld gezeigt hat: Der ganze
Sand fließt zu einem Punkt.
:::
::::

::::level (start := "bernoulli p") (target := "pure false") (moves := "not, heads") (lean := "((bernoulli p h).map (fun _ => true)).map not = pure false") (leanTarget := "DiscreteMeasure.pure false") (no := "1.3") (proof := "(p : I) : not <$> ((fun _ => true) <$> coin p) = pure false")
:::en
*Surely `false`, but there is no “always `false`”.* Two moves one after the other: the image measure of
the image measure is the image measure of the composition, $`(P \circ f^{-1}) \circ g^{-1} = P \circ (g \circ f)^{-1}`.
:::

:::de
*Sicher `false`, aber es gibt kein „immer `false`“.* Zwei Züge nacheinander: Das Bildmaß des Bildmaßes ist
das Bildmaß der Verkettung, $`(P \circ f^{-1}) \circ g^{-1} = P \circ (g \circ f)^{-1}`.
:::

:::proofen
Two new tools. The rule `map_pure : f <$> pure a = pure (f a)`: a move on a point mass moves the
point. And the tactic `rfl`, which closes a goal whose two sides are the same after computing: `!true`
is `false`.

*Tip.* `rw [coin_const]`, then `rw [map_pure]` (or both at once: `rw [coin_const, map_pure]`), then
`rfl`.
:::

:::proofde
Zwei neue Werkzeuge. Die Regel `map_pure : f <$> pure a = pure (f a)`: Ein Zug auf einer
Punktmasse verschiebt den Punkt. Und die Taktik `rfl`, die ein Ziel schließt, dessen beide Seiten
nach Ausrechnen gleich sind: `!true` ist `false`.

*Tipp.* `rw [coin_const]`, dann `rw [map_pure]` (oder beides auf einmal: `rw [coin_const, map_pure]`),
dann `rfl`.
:::
::::

::::level (start := "bernoulli p") (target := "nat 1:p 0:1-p") (moves := "not, toNat") (lean := "(bernoulli p h).map Bool.toNat 1 = p") (leanTarget := "map Bool.toNat (coin p)") (no := "1.4") (proof := "(p : I) : Bool.toNat <$> coin p = (fun b => if b then 1 else 0) <$> coin p")
:::en
*From sides to numbers.* `Bool.toNat` counts `true` as $`1` and `false` as $`0`: the distribution
moves to the natural numbers. This is how a coin becomes a random number.
:::

:::de
*Von Seiten zu Zahlen.* `Bool.toNat` zählt `true` als $`1` und `false` als $`0`: Die Verteilung
wandert zu den natürlichen Zahlen. So wird aus einer Münze eine Zufallszahl.
:::

:::proofen
`Bool.toNat` counts `true` as $`1` and `false` as $`0`. Both sides move the same coin, with two
maps that agree. Three new tactics: `congr 1` reduces the goal to the two maps being equal;
`funext b` to their being equal at every `b`; `cases b` splits into the cases `false` and `true`, two
goals, one after the other.

*Tip.* `congr 1`, `funext b`, `cases b`, `rfl`, `rfl`.
:::

:::proofde
`Bool.toNat` zählt `true` als $`1` und `false` als $`0`. Beide Seiten bewegen dieselbe Münze, mit
zwei Abbildungen, die übereinstimmen. Drei neue Taktiken: `congr 1` führt das Ziel darauf zurück,
dass die beiden Abbildungen gleich sind; `funext b` darauf, dass sie an jeder Stelle `b` gleich sind;
`cases b` teilt in die Fälle `false` und `true`, zwei Ziele, eines nach dem anderen.

*Tipp.* `congr 1`, `funext b`, `cases b`, `rfl`, `rfl`.
:::
::::

::::level (start := "bernoulli p") (target := "nat 1:1-p 0:p") (moves := "not, toNat") (lean := "((bernoulli p h).map not).map Bool.toNat 1 = 1 - p") (leanTarget := "map Bool.toNat (coin (σ p))") (no := "1.5") (proof := "(p : I) : Bool.toNat <$> (not <$> coin p) = Bool.toNat <$> coin (σ p)")
:::en
*The order matters.* Once the coin has become a number, it cannot be flipped any more.
:::

:::de
*Die Reihenfolge zählt.* Ist die Münze erst eine Zahl, lässt sie sich nicht mehr umdrehen.
:::

:::proofen
Nothing new: `rw` also finds the left side of a rule inside a bigger term.
:::

:::proofde
Nichts Neues: `rw` findet die linke Seite einer Regel auch in einem größeren Term.
:::
::::

::::level (start := "bernoulli p") (target := "int 5:p -2:1-p") (moves := "not, toNat, payoff 5 -2") (lean := "(bernoulli p h).map (fun b => if b then (5 : ℤ) else -2) 5 = p") (leanTarget := "map (fun b => if b = true then (5 : ℤ) else -2) (coin p)") (no := "1.6") (proof := "(p : I) : (fun b => if b then (5 : ℤ) else -2) <$> coin p = (fun n : ℕ => 7 * (n : ℤ) - 2) <$> (Bool.toNat <$> coin p)")
:::en
*A bet.* `true` wins 5 euros, `false` loses 2. The image measure is the distribution of your gain.
:::

:::de
*Eine Wette.* Bei `true` gewinnst du 5 Euro, bei `false` verlierst du 2. Das Bildmaß ist die Verteilung
deines Gewinns.
:::

:::proofen
The bet is $`7 \cdot (\text{the coin as a number}) - 2`. The new rule
`map_map : g <$> (f <$> μ) = (fun x => g (f x)) <$> μ`: two moves are one move.

*Tip.* `rw [map_map]`, then as in level 4.
:::

:::proofde
Die Wette ist $`7 \cdot (\text{die Münze als Zahl}) - 2`. Die neue Regel
`map_map : g <$> (f <$> μ) = (fun x => g (f x)) <$> μ`: Zwei Züge sind ein Zug.

*Tipp.* `rw [map_map]`, dann wie in Level 4.
:::
::::

::::level (start := "bernoulli p") (target := "int 5:1-p -2:p") (moves := "not, toNat, payoff 5 -2") (lean := "((bernoulli p h).map not).map (fun b => if b then (5 : ℤ) else -2) 5 = 1 - p") (leanTarget := "map (fun b => if b = true then (5 : ℤ) else -2) (coin (σ p))") (no := "1.7") (proof := "(p : I) : (fun b => if b then (5 : ℤ) else -2) <$> (not <$> coin p) = (fun b => if b then (5 : ℤ) else -2) <$> coin (σ p)")
:::en
*A better bet.* Make winning the likely outcome.
:::

:::de
*Eine bessere Wette.* Mach den Gewinn zum wahrscheinlichen Ausgang.
:::

:::proofen
The better bet is the bet on the flipped coin: $`1 - p` instead of $`p`.
:::

:::proofde
Die bessere Wette ist die Wette auf die umgedrehte Münze: $`1 - p` statt $`p`.
:::
::::

::::level (start := "bernoulli p") (target := "nat 0:1") (moves := "not, heads, tails, toNat") (lean := "((bernoulli p h).map (fun _ => false)).map Bool.toNat = pure 0") (leanTarget := "DiscreteMeasure.pure 0") (no := "1.8") (proof := "(p : I) : Bool.toNat <$> ((fun _ => false) <$> coin p) = pure 0")
:::en
*Surely zero.* A point mass on the numbers, however you get there.
:::

:::de
*Sicher null.* Eine Punktmasse auf den Zahlen, egal auf welchem Weg.
:::

:::proofen
World 1 in one proof.
:::

:::proofde
Welt 1 in einem Beweis.
:::
::::
