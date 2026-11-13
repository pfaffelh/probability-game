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

The coin is thrown. *Throw 100 times* throws it a hundred times, for the $`p` of the picture, and plays your moves on
what it shows; the frequencies, the thin bars beside the masses, come close to the masses.
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

Die Münze wird geworfen. *100-mal werfen* wirft sie hundertmal, für das $`p` des Bilds, und spielt deine Züge auf
dem, was sie zeigt; die Häufigkeiten, die schmalen Säulen neben den Massen, kommen den Massen nahe.
:::

::::circuit (inputs := "x") (gates := "not") (coins := "p") (target := "bool true:1-p false:p") (context := "Lean/Rules.lean") (proof := "(p : I) : (not <$> coin p) true = σ p") (lemma := "coin_not_true") (new := "rw, coin_true, coin_false, map_true, Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false, zero_add, Bool.not_not") (play := "a=not; x>a.0; a>out")
:::en
*Where does the mass go?* The coin `x` is thrown at the top; below, the output with the target:
`false` with mass $`p`, `true` with $`1 - p`. Put a `not` between them. Then look at `true`: its mass
came from `false`.
:::

:::de
*Wohin geht die Masse?* Oben wird die Münze `x` geworfen; unten der Ausgang mit dem Ziel: `false`
mit Masse $`p`, `true` mit $`1 - p`. Setz ein `nicht` dazwischen. Dann sieh dir `true` an: Seine
Masse kam von `false`.
:::

:::proofen
*Now the proof.* In Lean a distribution is a measure: `μ : DiscreteMeasure Bool` gives each point
of `Bool` its mass, and `μ x` is the mass of `μ` at `x`, the height of its bar. The coin is
`coin p`, and `f <$> μ` is the image measure of `μ` under `f`: the move `f` applied to the
distribution `μ`. `p : I` says that $`p` lies in the unit interval $`I = [0, 1]`, `σ p` is $`1 - p`,
and `↑p` is the number $`p` as a mass. Below is the *goal*, what is to be shown, and above it the
hypotheses (here only `p`).

The rule of moves:
`map_true : (f <$> μ) true = (bif f true then μ true else 0) + (bif f false then μ false else 0)`.
The mass at `true` comes from `true` when `f true` is `true`, and from `false` when `f false` is
`true`; `bif c then a else b` is `a` when `c` is `true`, and `b` when it is `false`.

What is left is computing, one rule after another: `Bool.not_true : (!true) = false`,
`Bool.not_false : (!false) = true`, `Bool.cond_false : (bif false then a else b) = b`,
`Bool.cond_true : (bif true then a else b) = a`, `zero_add : 0 + a = a`, and
`coin_false : (coin p) false = ↑(σ p)`. Your result becomes the lemma `coin_not_true`.

*Tip.* `rw [map_true]`, `rw [Bool.not_true, Bool.not_false]`,
`rw [Bool.cond_false, Bool.cond_true, zero_add]`, `rw [coin_false]` (type it, or tap the inventory,
and press *Run*).
:::

:::proofde
*Jetzt der Beweis.* In Lean ist eine Verteilung ein Maß: `μ : DiscreteMeasure Bool` gibt jedem
Punkt von `Bool` seine Masse, und `μ x` ist die Masse von `μ` in `x`, die Höhe seiner Säule. Die
Münze ist `coin p`, und `f <$> μ` ist das Bildmaß von `μ` unter `f`: der Zug `f`, angewandt auf die
Verteilung `μ`. `p : I` sagt, dass $`p` im Einheitsintervall $`I = [0, 1]` liegt, `σ p` ist
$`1 - p`, und `↑p` ist die Zahl $`p` als Masse. Unten steht das *Ziel*, also das, was zu zeigen ist,
und darüber die Annahmen (hier nur `p`).

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
:::solution
```
rw [map_true]
rw [Bool.not_true, Bool.not_false]
rw [Bool.cond_false, Bool.cond_true, zero_add]
rw [coin_false]
```
:::
::::

::::level (start := "bernoulli p") (target := "pure true") (moves := "not, heads") (lean := "(bernoulli p h).map (fun _ => true) = pure true") (leanTarget := "DiscreteMeasure.pure true") (proof := "(p : I) (b : Bool) : (fun _ => b) <$> coin p = pure b") (lemma := "coin_const") (new := "apply, cases, bool_ext, coin_total, pure_true") (play := "heads")
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

On the two points `false` and `true`, the bar at `true` decides everything: the rest of the mass
lies at `false`, since the total mass is $`1` (`Prob μ`). This is the first rule of the game,
`bool_ext μ ν (h : μ true = ν true) : μ = ν`. The tactic `apply bool_ext` turns a goal `μ = ν` into
what the rule needs: `μ true = ν true`.

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

Auf den zwei Punkten `false` und `true` entscheidet die Säule bei `true` alles: Der Rest der Masse
liegt bei `false`, denn die Gesamtmasse ist $`1` (`Prob μ`). Das ist die erste Regel des Spiels,
`bool_ext μ ν (h : μ true = ν true) : μ = ν`. Die Taktik `apply bool_ext` macht aus einem Ziel
`μ = ν` das, was die Regel braucht: `μ true = ν true`.

Vergleiche die Säulen bei `true`: `apply bool_ext`, dann `map_true` und die neue Regel
`pure_true : (pure b) true = bif b then 1 else 0`. Dann muss `b` bekannt sein: Die neue Taktik
`cases b` teilt in die Fälle `false` und `true`, zwei Ziele, eines nach dem anderen. Für `true` sagt
die neue Regel `coin_total : (coin p) true + (coin p) false = 1`, dass die Münze die Gesamtmasse
eins hat. `rw [Bool.cond_true]` schreibt immer nur ein `bif` um.

*Tipp.* `apply bool_ext`, `rw [map_true, pure_true]`, `cases b`, dann
`rw [Bool.cond_false, Bool.cond_false, Bool.cond_false, zero_add]` und
`rw [Bool.cond_true, Bool.cond_true, Bool.cond_true, coin_total]`.
:::
:::solution
```
apply bool_ext
rw [map_true, pure_true]
cases b
rw [Bool.cond_false, Bool.cond_false, Bool.cond_false, zero_add]
rw [Bool.cond_true, Bool.cond_true, Bool.cond_true, coin_total]
```
:::
::::

::::level (start := "bernoulli p") (target := "pure false") (moves := "not, heads") (lean := "((bernoulli p h).map (fun _ => true)).map not = pure false") (leanTarget := "DiscreteMeasure.pure false") (proof := "(p : I) : not <$> ((fun _ => true) <$> coin p) = pure false") (new := "rfl, map_pure") (play := "heads, not")
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
:::solution
```
rw [coin_const]
rw [map_pure]
rfl
```
:::
::::

::::level (start := "bernoulli p") (target := "nat 1:p 0:1-p") (moves := "not, toNat") (lean := "(bernoulli p h).map Bool.toNat 1 = p") (leanTarget := "map Bool.toNat (coin p)") (proof := "(p : I) : Bool.toNat <$> coin p = (fun b => if b then 1 else 0) <$> coin p") (new := "congr, funext, <;>") (play := "toNat")
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
`funext b` to their being equal at every `b`; and `cases b` (from *Always `true`*) splits into the cases `false` and `true`, two
goals, one after the other. New: `t₁ <;> t₂` runs `t₂` on every goal that `t₁` leaves, so
`cases b <;> rfl` does both cases in one line.

*Tip.* `congr 1`, `funext b`, `cases b <;> rfl`.
:::

:::proofde
`Bool.toNat` zählt `true` als $`1` und `false` als $`0`. Beide Seiten bewegen dieselbe Münze, mit
zwei Abbildungen, die übereinstimmen. Zwei neue Taktiken: `congr 1` führt das Ziel darauf zurück,
dass die beiden Abbildungen gleich sind; `funext b` darauf, dass sie an jeder Stelle `b` gleich sind;
und `cases b` (aus *Immer `true`*) teilt in die Fälle `false` und `true`, zwei Ziele, eines nach dem anderen. Neu: `t₁ <;> t₂` führt `t₂` auf jedem Ziel aus, das `t₁` übrig lässt; so erledigt
`cases b <;> rfl` beide Fälle in einer Zeile.

*Tipp.* `congr 1`, `funext b`, `cases b <;> rfl`.
:::
:::solution
```
congr 1
funext b
cases b <;> rfl
```
:::
::::

::::level (start := "bernoulli p") (target := "nat 0:1") (moves := "not, heads, tails, toNat") (lean := "((bernoulli p h).map (fun _ => false)).map Bool.toNat = pure 0") (leanTarget := "DiscreteMeasure.pure 0") (proof := "(p : I) : Bool.toNat <$> ((fun _ => false) <$> coin p) = pure 0") (play := "tails, toNat")
:::en
*Surely zero.* A point mass on the numbers, however you get there.
:::

:::de
*Sicher null.* Eine Punktmasse auf den Zahlen, egal auf welchem Weg.
:::

:::proofen
As in *Surely `false`* and *From sides to numbers*, now with a number.
:::

:::proofde
Wie in *Sicher `false`* und *Von Seiten zu Zahlen*, jetzt mit einer Zahl.
:::
:::solution
```
rw [coin_const, map_pure]
rfl
```
:::
::::

:::::only (edition := "main")
::::level (start := "bernoulli p") (target := "bernoulli 1-p") (moves := "not, heads, tails, toNat") (lean := "(bernoulli p h).map not = bernoulli (1 - p) tsub_le_self") (leanTarget := "coin (σ p)") (proof := "(p : I) : not <$> coin p = coin (σ p)") (lemma := "coin_not") (play := "not")
:::en
*The boss: flip the coin.* Not just the bar at `true`: the whole coin.
:::

:::de
*Der Endgegner: Dreh die Münze um.* Nicht nur die Säule bei `true`: die ganze Münze.
:::

:::proofen
Flipping turns the coin `p` into the coin $`1 - p`. Two distributions on `Bool` are the same when
their bars at `true` are (`bool_ext`, from *Always `true`*), and you know the bar at `true` of the flipped
coin (`coin_not_true`, from *Where does the mass go?*). Your result becomes the lemma `coin_not`, which the next worlds use
all the time.

*Tip.* `apply bool_ext`, then `rw` with your lemma and `coin_true`.
:::

:::proofde
Umdrehen macht aus der Münze $`p` die Münze $`1 - p`. Zwei Verteilungen auf `Bool` sind gleich, wenn
ihre Säulen bei `true` gleich sind (`bool_ext`, aus *Immer `true`*), und die Säule bei `true` der umgedrehten
Münze kennst du (`coin_not_true`, aus *Wohin geht die Masse?*). Dein Ergebnis wird das Lemma `coin_not`, das die nächsten
Welten ständig benutzen.

*Tipp.* `apply bool_ext`, dann `rw` mit deinem Lemma und `coin_true`.
:::
:::solution
```
apply bool_ext
rw [coin_not_true, coin_true]
```
:::
::::
:::::

:::::only (edition := "show")
::::level (start := "bernoulli p") (target := "nat 1:1-p 0:p") (moves := "not, heads, tails, toNat") (play := "not, toNat")
:::en
*The boss: count the `false`.* $`1` when the coin shows `false`, $`0` when it shows `true`. Two moves
of this world, one after the other.
:::

:::de
*Der Endgegner: Zähl die `false`.* $`1`, wenn die Münze `false` zeigt, $`0`, wenn sie `true` zeigt.
Zwei Züge dieser Welt, einer nach dem anderen.
:::
::::
:::::
