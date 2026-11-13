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
Lean, where a coin is a random `Bool`. Its distribution gives each outcome its *mass*, here $`1 - p`
and $`p`; the masses add up to $`1`. A distribution is the same as a probability measure.

The board is played from top to bottom, as in *Circuits*: at the top the coin `x ← coin p` is thrown,
below it the gates, at the bottom the output box with the target. A gate applies a map $`f` to the
outcome: the mass of each outcome goes to its image, and where several outcomes have the same image,
their masses add up. What comes out is the distribution of $`f(X)`, the *image measure*
$`P \circ f^{-1}`: $`P(f(X) = b) = P(X \in f^{-1}(\{b\}))`. The output box shows the target and your
output, as masses and as a small histogram (the target dashed); beside the board the bars for an
example $`p` (the slider changes it), and *Throw 100 times*: the coin thrown a hundred times, the
frequencies close to the masses.
:::

:::de
Eine Münze zeigt `true` mit Wahrscheinlichkeit $`p` und `false` mit Wahrscheinlichkeit $`1 - p`, für
ein beliebiges $`p`, wie in Lean, wo eine Münze ein zufälliges `Bool` ist. Ihre Verteilung gibt jedem
Ergebnis seine *Masse*, hier $`1 - p` und $`p`; die Massen ergeben zusammen $`1`. Eine Verteilung ist
dasselbe wie ein Wahrscheinlichkeitsmaß.

Das Spielfeld wird von oben nach unten gespielt, wie in *Schaltungen*: Oben wird die Münze
`x ← coin p` geworfen, darunter die Bausteine, unten der Ausgabekasten mit dem Ziel. Ein Baustein wendet
eine Abbildung $`f` auf das Ergebnis an: Die Masse jedes Ergebnisses geht zu seinem Bild, und wo mehrere
Ergebnisse dasselbe Bild haben, addieren sich ihre Massen. Was herauskommt, ist die Verteilung von
$`f(X)`, das *Bildmaß* $`P \circ f^{-1}`: $`P(f(X) = b) = P(X \in f^{-1}(\{b\}))`. Der Ausgabekasten
zeigt Ziel und Ausgang, als Massen und als kleines Histogramm (das Ziel gestrichelt); neben dem
Spielfeld die Säulen für ein Beispiel-$`p` (der Schieberegler ändert es) und *100-mal werfen*: die
Münze hundertmal geworfen, die Häufigkeiten nahe bei den Massen.
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

The rule of gates (maps):
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
Münze ist `coin p`, und `f <$> μ` ist das Bildmaß von `μ` unter `f`: der Baustein `f`, angewandt auf die
Verteilung `μ`. `p : I` sagt, dass $`p` im Einheitsintervall $`I = [0, 1]` liegt, `σ p` ist
$`1 - p`, und `↑p` ist die Zahl $`p` als Masse. Unten steht das *Ziel*, also das, was zu zeigen ist,
und darüber die Annahmen (hier nur `p`).

Die Regel der Bausteine (Abbildungen):
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

::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] : μ false = 1 - μ true") (lemma := "mass_false") (new := "mass_total, mass_ne_top, ENNReal.add_sub_cancel_left, exact")
:::en
*What is not at true.* Now in Lean only: a statement about *every* distribution on `Bool`, which no
board can show.
:::

:::de
*Was nicht bei true liegt.* Jetzt nur in Lean: eine Aussage über *jede* Verteilung auf `Bool`, die
kein Spielfeld zeigen kann.
:::

:::proofen
`μ : DiscreteMeasure Bool` is any distribution on `Bool`, and `[Prob μ]` says that its total mass is
one. That is the rule `mass_total μ : μ true + μ false = 1`. So the mass at `false` is what is
missing at `true`. Masses are numbers in $`[0, \infty]` (`ENNReal`); taking away is allowed when
what is taken away is finite: `ENNReal.add_sub_cancel_left (h : a ≠ ⊤) : a + b - a = b`, and
`mass_ne_top : μ b ≠ ⊤` says that a mass is finite. `rw [← mass_total μ]` rewrites from right
to left: the `1` becomes `μ true + μ false`. A rule with a hypothesis can also be used without it:
`rw [ENNReal.add_sub_cancel_left]` then leaves the hypothesis as a second goal, and `exact h` closes a
goal that is exactly `h`.

*Tip.* `rw [← mass_total μ]`, then `rw [ENNReal.add_sub_cancel_left mass_ne_top]` (or
`rw [ENNReal.add_sub_cancel_left]` and `exact mass_ne_top`). Type `\l` for `←`.
:::

:::proofde
`μ : DiscreteMeasure Bool` ist irgendeine Verteilung auf `Bool`, und `[Prob μ]` sagt, dass ihre
Gesamtmasse eins ist. Das ist die Regel `mass_total μ : μ true + μ false = 1`. Also ist die Masse bei
`false` das, was bei `true` zu eins fehlt. Massen sind Zahlen in $`[0, \infty]` (`ENNReal`);
wegnehmen darf man, wenn das Weggenommene endlich ist:
`ENNReal.add_sub_cancel_left (h : a ≠ ⊤) : a + b - a = b`, und `mass_ne_top : μ b ≠ ⊤` sagt,
dass eine Masse endlich ist. `rw [← mass_total μ]` schreibt von rechts nach links um: Die `1` wird zu
`μ true + μ false`. Eine Regel mit Annahme geht auch ohne sie: `rw [ENNReal.add_sub_cancel_left]`
lässt die Annahme dann als zweites Ziel übrig, und `exact h` schließt ein Ziel, das genau `h` ist.

*Tipp.* `rw [← mass_total μ]`, dann `rw [ENNReal.add_sub_cancel_left mass_ne_top]` (oder
`rw [ENNReal.add_sub_cancel_left]` und `exact mass_ne_top`). `\l` tippen für `←`.
:::
:::solution
```
rw [← mass_total μ]
rw [ENNReal.add_sub_cancel_left mass_ne_top]
```
:::
::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] : μ true = 1 - μ false") (lemma := "mass_true") (new := "add_comm")
:::en
*What is not at false.* The same the other way round.
:::

:::de
*Was nicht bei false liegt.* Dasselbe andersherum.
:::

:::proofen
As before, but now `μ false` is taken away, and in `μ true + μ false` it stands second. The rule
`add_comm : a + b = b + a` turns the sum round.

*Tip.* `rw [← mass_total μ]`, `rw [add_comm]`, then `ENNReal.add_sub_cancel_left` as before.
:::

:::proofde
Wie eben, aber jetzt wird `μ false` weggenommen, und in `μ true + μ false` steht es an zweiter
Stelle. Die Regel `add_comm : a + b = b + a` dreht die Summe um.

*Tipp.* `rw [← mass_total μ]`, `rw [add_comm]`, dann `ENNReal.add_sub_cancel_left` wie eben.
:::
:::solution
```
rw [← mass_total μ]
rw [add_comm]
rw [ENNReal.add_sub_cancel_left mass_ne_top]
```
:::
::::

::::leanonly (proof := "(μ ν : DiscreteMeasure Bool) [Prob μ] [Prob ν] (h : μ true = ν true) : μ = ν") (lemma := "bool_ext") (new := "ext, cases")
:::en
*One bar is enough.* Two distributions on `Bool` with the same mass at `true` are the same. That is
why the board only had to look at one bar.
:::

:::de
*Eine Säule reicht.* Zwei Verteilungen auf `Bool` mit derselben Masse bei `true` sind gleich. Darum
musste das Spielfeld nur auf eine Säule schauen.
:::

:::proofen
Now there is a hypothesis: `h : μ true = ν true`. Two new tactics. `ext x`: two distributions are
equal when they have the same mass at every point `x`. `cases x`: the point is `false` or `true`, two
goals one after the other. And `exact h` (from level 2). At `false`, your lemma
`mass_false` helps, twice, and then `h`.

*Tip.* `ext x`, `cases x`, then `rw [mass_false, mass_false, h]`, and `exact h`.
:::

:::proofde
Jetzt gibt es eine Annahme: `h : μ true = ν true`. Zwei neue Taktiken. `ext x`: Zwei Verteilungen sind
gleich, wenn sie an jedem Punkt `x` dieselbe Masse haben. `cases x`: Der Punkt ist `false` oder `true`,
zwei Ziele nacheinander. Und `exact h` (aus Level 2). Bei `false` hilft dein Lemma
`mass_false`, zweimal, und dann `h`.

*Tipp.* `ext x`, `cases x`, dann `rw [mass_false, mass_false, h]`, und `exact h`.
:::
:::solution
```
ext x
cases x
rw [mass_false, mass_false, h]
exact h
```
:::
::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] : μ = coin (chance μ)") (lemma := "eq_coin") (new := "apply, chance, chance_eq")
:::en
*Every distribution is a coin.* Whatever distribution on `Bool`: it is the coin with its mass at
`true`.
:::

:::de
*Jede Verteilung ist eine Münze.* Welche Verteilung auf `Bool` auch immer: Sie ist die Münze mit ihrer
Masse bei `true`.
:::

:::proofen
`coin` takes a number in $`[0, 1]`, a mass is a number in $`[0, \infty]`. `chance μ` is the mass at
`true` as a number in $`[0, 1]`, and `chance_eq : ↑(chance μ) = μ true`. The tactic `apply bool_ext`
turns the goal `μ = ν` into what your lemma needs: `μ true = ν true`.

*Tip.* `apply bool_ext`, then `rw [coin_true, chance_eq]`.
:::

:::proofde
`coin` nimmt eine Zahl in $`[0, 1]`, eine Masse ist eine Zahl in $`[0, \infty]`. `chance μ` ist die
Masse bei `true` als Zahl in $`[0, 1]`, und `chance_eq : ↑(chance μ) = μ true`. Die Taktik
`apply bool_ext` macht aus dem Ziel `μ = ν` das, was dein Lemma braucht: `μ true = ν true`.

*Tipp.* `apply bool_ext`, dann `rw [coin_true, chance_eq]`.
:::
:::solution
```
apply bool_ext
rw [coin_true, chance_eq]
```
:::
::::

::::circuit (inputs := "x") (gates := "not, alwaysT") (coins := "p") (target := "pure true") (context := "Lean/Rules.lean") (proof := "(p : I) (b : Bool) : (fun _ => b) <$> coin p = pure b") (lemma := "coin_const") (new := "coin_total, pure_true") (play := "a=alwaysT; x>a.0; a>out")
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

On the two points `false` and `true`, the bar at `true` decides everything: that is your lemma
`bool_ext`, and `apply bool_ext` turns the goal into `μ true = ν true`.

Compare the bars at `true`: `apply bool_ext`, then `map_true`, and
the new rule `pure_true : (pure b) true = bif b then 1 else 0`. Then `b` has to be known: `cases b`. For
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

Auf den zwei Punkten `false` und `true` entscheidet die Säule bei `true` alles: Das ist dein Lemma
`bool_ext`, und `apply bool_ext` macht aus dem Ziel `μ true = ν true`.

Vergleiche die Säulen bei `true`: `apply bool_ext`, dann `map_true` und die neue Regel
`pure_true : (pure b) true = bif b then 1 else 0`. Dann muss `b` bekannt sein: `cases b`. Für `true` sagt
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

::::circuit (inputs := "x") (gates := "not, alwaysT") (coins := "p") (target := "pure false") (context := "Lean/Rules.lean") (proof := "(p : I) : not <$> ((fun _ => true) <$> coin p) = pure false") (new := "rfl, map_pure") (play := "a=alwaysT; b=not; x>a.0; a>b.0; b>out")
:::en
*Surely `false`, but there is no “always `false`”.* Two gates one after the other: the image measure of
the image measure is the image measure of the composition, $`(P \circ f^{-1}) \circ g^{-1} = P \circ (g \circ f)^{-1}`.
:::

:::de
*Sicher `false`, aber es gibt kein „immer `false`“.* Zwei Bausteine nacheinander: Das Bildmaß des Bildmaßes ist
das Bildmaß der Verkettung, $`(P \circ f^{-1}) \circ g^{-1} = P \circ (g \circ f)^{-1}`.
:::

:::proofen
Two new tools. The rule `map_pure : f <$> pure a = pure (f a)`: a gate on a point mass moves the
point. And the tactic `rfl`, which closes a goal whose two sides are the same after computing: `!true`
is `false`.

*Tip.* `rw [coin_const]`, then `rw [map_pure]` (or both at once: `rw [coin_const, map_pure]`), then
`rfl`.
:::

:::proofde
Zwei neue Werkzeuge. Die Regel `map_pure : f <$> pure a = pure (f a)`: Ein Baustein auf einer
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

::::circuit (inputs := "x") (gates := "not, toNat") (coins := "p") (target := "nat 0:1-p 1:p") (context := "Lean/Rules.lean") (proof := "(p : I) : Bool.toNat <$> coin p = (fun b => if b then 1 else 0) <$> coin p") (new := "congr, funext, <;>") (play := "a=toNat; x>a.0; a>out")
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

::::circuit (inputs := "x") (gates := "not, alwaysT, alwaysF, toNat") (coins := "p") (target := "pure 0") (context := "Lean/Rules.lean") (proof := "(p : I) : Bool.toNat <$> ((fun _ => false) <$> coin p) = pure 0") (play := "a=alwaysF; b=toNat; x>a.0; a>b.0; b>out")
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
::::circuit (inputs := "x") (gates := "not, alwaysT, alwaysF, toNat") (coins := "p") (target := "bernoulli 1-p") (context := "Lean/Rules.lean") (proof := "(p : I) : not <$> coin p = coin (σ p)") (lemma := "coin_not") (play := "a=not; x>a.0; a>out")
:::en
*The boss: flip the coin.* Not just the bar at `true`: the whole coin.
:::

:::de
*Der Endgegner: Dreh die Münze um.* Nicht nur die Säule bei `true`: die ganze Münze.
:::

:::proofen
Flipping turns the coin `p` into the coin $`1 - p`. Two distributions on `Bool` are the same when
their bars at `true` are (`bool_ext`, your lemma), and you know the bar at `true` of the flipped
coin (`coin_not_true`, from *Where does the mass go?*). Your result becomes the lemma `coin_not`, which the next worlds use
all the time.

*Tip.* `apply bool_ext`, then `rw` with your lemma and `coin_true`.
:::

:::proofde
Umdrehen macht aus der Münze $`p` die Münze $`1 - p`. Zwei Verteilungen auf `Bool` sind gleich, wenn
ihre Säulen bei `true` gleich sind (`bool_ext`, dein Lemma), und die Säule bei `true` der umgedrehten
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
::::circuit (inputs := "x") (gates := "not, alwaysT, alwaysF, toNat") (coins := "p") (target := "nat 0:p 1:1-p") (context := "Lean/Rules.lean") (play := "a=not; b=toNat; x>a.0; a>b.0; b>out")
:::en
*The boss: count the `false`.* $`1` when the coin shows `false`, $`0` when it shows `true`. Two gates
of this world, one after the other.
:::

:::de
*Der Endgegner: Zähl die `false`.* $`1`, wenn die Münze `false` zeigt, $`0`, wenn sie `true` zeigt.
Zwei Bausteine dieser Welt, einer nach dem anderen.
:::
::::
:::::
