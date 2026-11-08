import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "One Coin" =>

%%%
htmlSplit := .never
%%%

:::en
A coin shows `true` with probability $`p` and `false` with probability $`1 - p`, for any $`p`, as in
Lean, where a coin is a random `Bool`. Its
distribution is drawn as two bars. A distribution is the same as a probability measure: it gives
each outcome its mass, here $`1 - p` and $`p`, and the masses add up to $`1`. A *move* applies a map
$`f` to the outcome: the mass of each outcome goes to its image, and where several outcomes have the
same image, their masses add up. What you get is the distribution of $`f(X)`, the *image measure* $`P \circ f^{-1}`:
$`P(f(X) = b) = P(X \in f^{-1}(\{b\}))`. Tap a bar to see where its mass came from.

Bring the distribution into the shape of the target, drawn on the right (and dashed on the board when it
lives on the same space). The masses are $`p` and $`1 - p`; the picture shows them for an example
$`p`, which the slider changes.
:::

:::de
Eine Münze zeigt `true` mit Wahrscheinlichkeit $`p` und `false` mit Wahrscheinlichkeit $`1 - p`, für
ein beliebiges $`p`, wie in Lean, wo eine Münze ein zufälliges `Bool` ist. Ihre Verteilung ist als zwei Säulen
gezeichnet. Eine Verteilung ist dasselbe wie ein Wahrscheinlichkeitsmaß: Sie gibt jedem Ergebnis
seine Masse, hier $`1 - p` und $`p`, und die Massen ergeben zusammen $`1`. Ein *Zug* wendet eine
Abbildung $`f` auf das Ergebnis an: Die Masse jedes Ergebnisses geht zu seinem Bild, und wo mehrere
Ergebnisse dasselbe Bild haben, addieren sich ihre Massen. Was herauskommt, ist die Verteilung von $`f(X)`, das
*Bildmaß* $`P \circ f^{-1}`: $`P(f(X) = b) = P(X \in f^{-1}(\{b\}))`. Tippe eine Säule an, um zu
sehen, woher ihre Masse kommt.

Bring die Verteilung in die Form des Ziels, das rechts gezeichnet ist (und gestrichelt auf dem Spielfeld,
wenn es auf demselben Raum lebt). Die Massen sind $`p` und $`1 - p`; das Bild zeigt sie für ein
Beispiel-$`p`, das der Schieberegler ändert.
:::

::::level (start := "bernoulli p") (target := "bernoulli p") (moves := "not") (lean := "((bernoulli p h).map not).map not = bernoulli p h") (leanTarget := "coin p") (no := "1.1") (proof := "(p : I) (μ : DiscreteMeasure Bool) [hμ : Prob μ] (h : μ true = p) : μ = coin p")
:::en
*Flip it twice.* `not` makes `true` into `false` and `false` into `true`: the two bars swap. Flip
twice, and the coin is back as it was. The board sees this by comparing the bars with the target.
:::

:::de
*Zweimal umdrehen.* `not` macht aus `true` `false` und aus `false` `true`: Die beiden Säulen tauschen.
Zweimal umgedreht, ist die Münze wieder wie vorher. Das Spielfeld sieht das, indem es die Säulen mit
dem Ziel vergleicht.
:::

:::proofen
*Now the proof.* In Lean a distribution is a measure: `μ : DiscreteMeasure Bool` gives each point
of `Bool` its mass. The coin is `coin p`, and `f <$> μ` is the image measure of `μ` under `f`:
the move `f` applied to the distribution `μ`; `σ p` is $`1 - p`, and `p : I` says that $`p` lies in
the unit interval $`I = [0, 1]`. `μ x` is the mass of `μ` at `x`, the height of its bar, and
`↑p` is the number $`p` as a mass. `Prob μ` says that `μ` is a probability measure, a distribution: its total mass is $`1`.
Below is the *goal*, what is to be shown, and above it the hypotheses, here `hμ` and `h`.

On the two points `false` and `true`, the bar at `true` decides everything: the rest of the mass lies at
`false`. This is the first rule of the game,
`bool_ext μ ν (h : μ true = ν true) : μ = ν`. So every distribution with mass $`p` at `true` is the
coin `coin p`, as the statement says.

The tactic `apply bool_ext` turns the goal `μ = coin p` into what the rule needs:
`μ true = (coin p) true`. The tactic `rw [h]` *rewrites* the goal with `h`: it replaces the left
side of `h` by its right side. The rule `coin_true : (coin p) true = ↑p` gives the mass of the coin.
When both sides of the goal are the same, the goal is closed.

*Tip.* `apply bool_ext`, then `rw [h, coin_true]` (type it, or tap the inventory, and press *Run*).
:::

:::proofde
*Jetzt der Beweis.* In Lean ist eine Verteilung ein Maß: `μ : DiscreteMeasure Bool` gibt jedem
Punkt von `Bool` seine Masse. Die Münze ist `coin p`, und `f <$> μ` ist das Bildmaß von `μ` unter
`f`: der Zug `f`, angewandt auf die Verteilung `μ`; `σ p` ist $`1 - p`, und `p : I` sagt, dass $`p`
im Einheitsintervall $`I = [0, 1]` liegt. `μ x` ist die Masse von `μ` in `x`, die Höhe seiner Säule,
und `↑p` ist die Zahl $`p` als Masse. `Prob μ` sagt, dass `μ` ein Wahrscheinlichkeitsmaß
ist, eine Verteilung: Die Gesamtmasse ist $`1`. Unten steht das *Ziel*, also das, was zu zeigen ist, und darüber die Annahmen, hier `hμ` und `h`.

Auf den zwei Punkten `false` und `true` entscheidet die Säule bei `true` alles: Der Rest der Masse liegt bei
`false`. Das ist die erste Regel des Spiels, `bool_ext μ ν (h : μ true = ν true) : μ = ν`. Also ist
jede Verteilung mit Masse $`p` bei `true` die Münze `coin p`, wie die Aussage sagt.

Die Taktik `apply bool_ext` macht aus dem Ziel `μ = coin p` das, was die Regel braucht:
`μ true = (coin p) true`. Die Taktik `rw [h]` *schreibt* das Ziel mit `h` *um*: Sie ersetzt die
linke Seite von `h` durch ihre rechte. Die Regel `coin_true : (coin p) true = ↑p` gibt die Masse der
Münze. Sind beide Seiten des Ziels gleich, ist das Ziel erledigt.

*Tipp.* `apply bool_ext`, dann `rw [h, coin_true]` (eintippen oder im Inventar antippen, dann
*Ausführen*).
:::
::::

::::level (start := "bernoulli p") (target := "bernoulli 1-p") (moves := "not") (lean := "(bernoulli p h).map not true = 1 - p") (leanTarget := "coin (σ p)") (no := "1.2") (proof := "(p : I) : (not <$> coin p) true = σ p") (lemma := "coin_not_true")
:::en
*Where does the mass go?* Flip the coin once, and look at the bar at `true`: its mass came from
`false`.
:::

:::de
*Wohin geht die Masse?* Dreh die Münze einmal um und sieh dir die Säule bei `true` an: Ihre Masse
kam von `false`.
:::

:::proofen
The rule of moves:
`map_true : (f <$> μ) true = (bif f true then μ true else 0) + (bif f false then μ false else 0)`.
The mass at `true` comes from `true` when `f true` is `true`, and from `false` when `f false` is
`true`; `bif c then a else b` is `a` when `c` is `true`, and `b` when it is `false`.

What is left is computing, one rule after another: `Bool.not_true : (!true) = false`,
`Bool.not_false : (!false) = true`, `Bool.cond_false : (bif false then a else b) = b`,
`Bool.cond_true : (bif true then a else b) = a`, `zero_add : 0 + a = a`, and
`coin_false : (coin p) false = ↑(σ p)`. Your result becomes the lemma `coin_not_true`.

*Tip.* `rw [map_true]`, `rw [Bool.not_true, Bool.not_false]`,
`rw [Bool.cond_false, Bool.cond_true, zero_add]`, `rw [coin_false]`.
:::

:::proofde
Die Regel der Züge:
`map_true : (f <$> μ) true = (bif f true then μ true else 0) + (bif f false then μ false else 0)`.
Die Masse bei `true` kommt von `true`, wenn `f true` gleich `true` ist, und von `false`, wenn
`f false` gleich `true` ist; `bif c then a else b` ist `a`, wenn `c` gleich `true` ist, und `b`,
wenn es `false` ist.

Der Rest ist Rechnen, eine Regel nach der anderen: `Bool.not_true : (!true) = false`,
`Bool.not_false : (!false) = true`, `Bool.cond_false : (bif false then a else b) = b`,
`Bool.cond_true : (bif true then a else b) = a`, `zero_add : 0 + a = a` und
`coin_false : (coin p) false = ↑(σ p)`. Dein Ergebnis wird das Lemma `coin_not_true`.

*Tipp.* `rw [map_true]`, `rw [Bool.not_true, Bool.not_false]`,
`rw [Bool.cond_false, Bool.cond_true, zero_add]`, `rw [coin_false]`.
:::
::::

::::level (start := "bernoulli p") (target := "pure true") (moves := "not, heads, tails") (lean := "(bernoulli p h).map (fun _ => true) = pure true") (leanTarget := "DiscreteMeasure.pure true") (no := "1.3") (proof := "(p : I) (b : Bool) : (fun _ => b) <$> coin p = pure b") (lemma := "coin_const")
:::en
*Always `true`.* A constant map sends both outcomes to the same point: all the mass goes together.
The result is sure, a point mass (Dirac measure).
:::

:::de
*Immer `true`.* Eine konstante Abbildung schickt beide Ergebnisse auf denselben Punkt: Die ganze Masse
kommt zusammen. Das Ergebnis ist sicher, eine Punktmasse (Dirac-Maß).
:::

:::proofen
`pure b` is the point mass at `b`, and `fun _ => b` is the constant map. The statement says what
the board showed, for both values `b`: all the mass goes to one point. It becomes your lemma
`coin_const`.

Compare the bars at `true`: `apply bool_ext`, then `map_true`, and
the new rule `pure_true : (pure b) true = bif b then 1 else 0`. Then `b` has to be known: the new
tactic `cases b` splits into the cases `false` and `true`, two goals, one after the other. For
`true`, the new rule `coin_total : (coin p) true + (coin p) false = 1` says that the coin has total
mass one. `rw [Bool.cond_true]` rewrites one `bif` at a time.

*Tip.* `apply bool_ext`, `rw [map_true, pure_true]`, `cases b`, then
`rw [Bool.cond_false, Bool.cond_false, Bool.cond_false, zero_add]` and
`rw [Bool.cond_true, Bool.cond_true, Bool.cond_true, coin_total]`.
:::

:::proofde
`pure b` ist die Punktmasse in `b`, und `fun _ => b` ist die konstante Abbildung. Die Aussage sagt,
was das Spielfeld gezeigt hat, für beide Werte `b`: Die ganze Masse geht zu einem Punkt. Sie wird
dein Lemma `coin_const`.

Vergleiche die Säulen bei `true`: `apply bool_ext`, dann `map_true` und die neue Regel
`pure_true : (pure b) true = bif b then 1 else 0`. Dann muss `b` bekannt sein: Die neue Taktik
`cases b` teilt in die Fälle `false` und `true`, zwei Ziele, eines nach dem anderen. Für `true` sagt
die neue Regel `coin_total : (coin p) true + (coin p) false = 1`, dass die Münze die Gesamtmasse
eins hat. `rw [Bool.cond_true]` schreibt immer nur ein `bif` um.

*Tipp.* `apply bool_ext`, `rw [map_true, pure_true]`, `cases b`, dann
`rw [Bool.cond_false, Bool.cond_false, Bool.cond_false, zero_add]` und
`rw [Bool.cond_true, Bool.cond_true, Bool.cond_true, coin_total]`.
:::
::::

::::level (start := "bernoulli p") (target := "pure false") (moves := "not, heads") (lean := "((bernoulli p h).map (fun _ => true)).map not = pure false") (leanTarget := "DiscreteMeasure.pure false") (no := "1.4") (proof := "(p : I) : not <$> ((fun _ => true) <$> coin p) = pure false")
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

::::level (start := "bernoulli p") (target := "nat 1:p 0:1-p") (moves := "not, toNat") (lean := "(bernoulli p h).map Bool.toNat 1 = p") (leanTarget := "map Bool.toNat (coin p)") (no := "1.5") (proof := "(p : I) : Bool.toNat <$> coin p = (fun b => if b then 1 else 0) <$> coin p")
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
maps that agree. Two new tactics: `congr 1` reduces the goal to the two maps being equal;
`funext b` to their being equal at every `b`; and `cases b` (from level 3) splits into the cases `false` and `true`, two
goals, one after the other.

*Tip.* `congr 1`, `funext b`, `cases b`, `rfl`, `rfl`.
:::

:::proofde
`Bool.toNat` zählt `true` als $`1` und `false` als $`0`. Beide Seiten bewegen dieselbe Münze, mit
zwei Abbildungen, die übereinstimmen. Zwei neue Taktiken: `congr 1` führt das Ziel darauf zurück,
dass die beiden Abbildungen gleich sind; `funext b` darauf, dass sie an jeder Stelle `b` gleich sind;
und `cases b` (aus Level 3) teilt in die Fälle `false` und `true`, zwei Ziele, eines nach dem anderen.

*Tipp.* `congr 1`, `funext b`, `cases b`, `rfl`, `rfl`.
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

*Tip.* `rw [map_map]`, then as in level 5.
:::

:::proofde
Die Wette ist $`7 \cdot (\text{die Münze als Zahl}) - 2`. Die neue Regel
`map_map : g <$> (f <$> μ) = (fun x => g (f x)) <$> μ`: Zwei Züge sind ein Zug.

*Tipp.* `rw [map_map]`, dann wie in Level 5.
:::
::::

::::level (start := "bernoulli p") (target := "nat 0:1") (moves := "not, heads, tails, toNat") (lean := "((bernoulli p h).map (fun _ => false)).map Bool.toNat = pure 0") (leanTarget := "DiscreteMeasure.pure 0") (no := "1.7") (proof := "(p : I) : Bool.toNat <$> ((fun _ => false) <$> coin p) = pure 0")
:::en
*Surely zero.* A point mass on the numbers, however you get there.
:::

:::de
*Sicher null.* Eine Punktmasse auf den Zahlen, egal auf welchem Weg.
:::

:::proofen
As in levels 3 and 4, now with a number.
:::

:::proofde
Wie in den Leveln 3 und 4, jetzt mit einer Zahl.
:::
::::

:::::only (edition := "main")
::::level (start := "bernoulli p") (target := "bernoulli 1-p") (moves := "not, heads, tails, toNat") (lean := "(bernoulli p h).map not = bernoulli (1 - p) tsub_le_self") (leanTarget := "coin (σ p)") (no := "1.8") (proof := "(p : I) : not <$> coin p = coin (σ p)") (lemma := "coin_not")
:::en
*The boss: flip the coin.* Not just the bar at `true`: the whole coin.
:::

:::de
*Der Endgegner: Dreh die Münze um.* Nicht nur die Säule bei `true`: die ganze Münze.
:::

:::proofen
Flipping turns the coin `p` into the coin $`1 - p`. Two distributions on `Bool` are the same when
their bars at `true` are (`bool_ext`, level 1), and you know the bar at `true` of the flipped
coin (`coin_not_true`, level 2). Your result becomes the lemma `coin_not`, which worlds 2 and 3 use
all the time.

*Tip.* `apply bool_ext`, then `rw` with your lemma and `coin_true`.
:::

:::proofde
Umdrehen macht aus der Münze $`p` die Münze $`1 - p`. Zwei Verteilungen auf `Bool` sind gleich, wenn
ihre Säulen bei `true` gleich sind (`bool_ext`, Level 1), und die Säule bei `true` der umgedrehten
Münze kennst du (`coin_not_true`, Level 2). Dein Ergebnis wird das Lemma `coin_not`, das die Welten
2 und 3 ständig benutzen.

*Tipp.* `apply bool_ext`, dann `rw` mit deinem Lemma und `coin_true`.
:::
::::
:::::

:::::only (edition := "show")
::::level (start := "bernoulli p") (target := "int 5:1-p -2:p") (moves := "not, heads, tails, toNat, payoff 5 -2")
:::en
*The boss: a bet on `false`.* You win $`5` when the coin shows `false`, and lose $`2` when it shows
`true`. Two moves of this world, one after the other.
:::

:::de
*Der Endgegner: eine Wette auf `false`.* Du gewinnst $`5`, wenn die Münze `false` zeigt, und
verlierst $`2`, wenn sie `true` zeigt. Zwei Züge dieser Welt, einer nach dem anderen.
:::
::::
:::::
