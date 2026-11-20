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

The board is played from top to bottom, as in *Bool*: at the top the coin `x ← coin p` is thrown,
below it the gates, at the bottom the output box with the target. A gate applies a map $`f` to the
outcome: the mass of each outcome goes to its image, and where several outcomes have the same image,
their masses add up. What comes out is the distribution of $`f(X)`, the *image measure*
$`P \circ f^{-1}`: $`P(f(X) = b) = P(X \in f^{-1}(\{b\}))`. The output box shows the target and your
output, as masses and as a small histogram (the target dashed), drawn for an example $`p`; the slider
in the bar at the bottom changes it.
:::

:::de
Eine Münze zeigt `true` mit Wahrscheinlichkeit $`p` und `false` mit Wahrscheinlichkeit $`1 - p`, für
ein beliebiges $`p`, wie in Lean, wo eine Münze ein zufälliges `Bool` ist. Ihre Verteilung gibt jedem
Ergebnis seine *Masse*, hier $`1 - p` und $`p`; die Massen ergeben zusammen $`1`. Eine Verteilung ist
dasselbe wie ein Wahrscheinlichkeitsmaß.

Das Spielfeld wird von oben nach unten gespielt, wie in *Bool*: Oben wird die Münze
`x ← coin p` geworfen, darunter die Bausteine, unten der Ausgabekasten mit dem Ziel. Ein Baustein wendet
eine Abbildung $`f` auf das Ergebnis an: Die Masse jedes Ergebnisses geht zu seinem Bild, und wo mehrere
Ergebnisse dasselbe Bild haben, addieren sich ihre Massen. Was herauskommt, ist die Verteilung von
$`f(X)`, das *Bildmaß* $`P \circ f^{-1}`: $`P(f(X) = b) = P(X \in f^{-1}(\{b\}))`. Der Ausgabekasten
zeigt Ziel und Ausgang, als Massen und als kleines Histogramm (das Ziel gestrichelt), gezeichnet für ein
Beispiel-$`p`; der Schieberegler in der Leiste unten ändert es.
:::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] (h : μ true = 0) : μ false = ⟦1 ‖ 0, 1⟧") (uses := "mass_total, zero_add, coin_total, add_zero, mul_zero")
:::hint (anchor := "none")
:::

:::en
*The whole mass.* A distribution has the total mass one. If nothing lies at `true`, everything lies at `false`.
:::

:::de
*Die ganze Masse.* Eine Verteilung hat die Gesamtmasse eins. Liegt bei `true` nichts, liegt alles bei `false`.
:::

:::proofen
`μ : DiscreteMeasure Bool` is any distribution on `Bool`, and `[Prob μ]` says that its total mass is one: your theorem `mass_total μ : μ true + μ false = 1`. `h : μ true = 0` is a hypothesis, a rule of this level only. `rw [← mass_total μ]` rewrites from right to left: the `1` becomes `μ true + μ false`. Then `h`, then `zero_add`.

*Tip.* `rw [← mass_total μ, h, zero_add]` (type `\l` for `←`, or tap ←).
:::

:::proofde
`μ : DiscreteMeasure Bool` ist irgendeine Verteilung auf `Bool`, und `[Prob μ]` sagt, dass ihre Gesamtmasse eins ist: dein Satz `mass_total μ : μ true + μ false = 1`. `h : μ true = 0` ist eine Annahme, eine Regel nur dieses Levels. `rw [← mass_total μ]` schreibt von rechts nach links um: Die `1` wird zu `μ true + μ false`. Dann `h`, dann `zero_add`.

*Tipp.* `rw [← mass_total μ, h, zero_add]` (`\l` tippen für `←`, oder ← antippen).
:::
:::solution
```
rw [← mass_total μ, h, zero_add]
```
:::
::::

:::::leanonly (proof := "(a b : ℝ≥0∞) : ⟦a - a + b ‖ a + b - a, b - a + a, a - a + b⟧ = b") (new := "tsub_self") (uses := "tsub_self, zero_add, add_zero, mul_zero")
:::en
*Subtracting masses.* In Lean, masses are numbers in `ℝ≥0∞ = [0, ∞]` (`ENNReal`). Adding is as
usual, with `a + ∞ = ∞`. But `a - b : ℝ≥0∞` cannot be negative: `a - b = 0` when `b > a`. And with
`∞`: `∞ - b = ∞` for a finite `b`, `a - ∞ = 0`, in particular `∞ - ∞ = 0`.
:::

:::de
*Massen abziehen.* In Lean sind Massen Zahlen in `ℝ≥0∞ = [0, ∞]` (`ENNReal`). Addieren geht wie
gewohnt, mit `a + ∞ = ∞`. Aber `a - b : ℝ≥0∞` kann nicht negativ sein: `a - b = 0`, wenn `b > a`. Und
mit `∞`: `∞ - b = ∞` für ein endliches `b`, `a - ∞ = 0`, insbesondere `∞ - ∞ = 0`.
:::

::::hint (anchor := "gap")
:::en
Which of the three holds for all `a b : ℝ≥0∞`? Try `b < a`, and try `a = ∞`.
:::

:::de
Welche der drei gilt für alle `a b : ℝ≥0∞`? Probier `b < a`, und probier `a = ∞`.
:::
::::

:::proofen
`b - a + a = b` fails for `b < a`: then `b - a = 0`, and `0 + a = a`. `a + b - a = b` fails for
`a = ∞`: `∞ + b - ∞ = ∞ - ∞ = 0`. It holds for every finite `a`: that is the rule `ENNReal.add_sub_cancel_left`, in *The rest of the mass*. But
`a - a = 0` always, also for `a = ∞`: the rule `tsub_self : a - a = 0`. Then `zero_add`.

*Tip.* `a - a + b`; then `rw [tsub_self, zero_add]`.
:::

:::proofde
`b - a + a = b` stimmt nicht für `b < a`: Dann ist `b - a = 0`, und `0 + a = a`. `a + b - a = b`
stimmt nicht für `a = ∞`: `∞ + b - ∞ = ∞ - ∞ = 0`. Für jedes endliche `a` gilt es: Das ist die Regel
`ENNReal.add_sub_cancel_left`, in *Der Rest der Masse*. Aber `a - a = 0` immer, auch für `a = ∞`: die Regel `tsub_self : a - a = 0`. Dann
`zero_add`.

*Tipp.* `a - a + b`; dann `rw [tsub_self, zero_add]`.
:::
:::solution
```
rw [tsub_self, zero_add]
```
:::
:::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] : μ false + μ true = 1") (uses := "add_comm, mass_total, add_assoc, coin_total")
:::en
*The other way round.* The total mass, with the summands swapped.
:::

:::de
*Andersherum.* Die Gesamtmasse, mit vertauschten Summanden.
:::

:::proofen
`add_comm : a + b = b + a` (from *Masses*) turns a sum round; then it is `mass_total μ`.

*Tip.* `rw [add_comm, mass_total μ]`.
:::

:::proofde
`add_comm : a + b = b + a` (aus *Massen*) dreht eine Summe um; dann ist es `mass_total μ`.

*Tipp.* `rw [add_comm, mass_total μ]`.
:::
:::solution
```
rw [add_comm, mass_total μ]
```
:::
::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] (b : Bool) : μ b = ⟦1 - μ (!b) ‖ 1 - μ (!b), μ (!b) - 1, 1 - μ b⟧") (lemma := "mass_not") (new := "ENNReal.add_sub_cancel_left") (uses := "Bool.not_false, mass_total, ENNReal.add_sub_cancel_left, mass_ne_top, Bool.not_true, add_comm, coin_total, add_assoc")
:::en
*The rest of the mass.* Now in Lean only: a statement about *every* distribution on `Bool`, which no
board can show. What is not at `b` lies at `!b`.
:::

:::de
*Der Rest der Masse.* Jetzt nur in Lean: eine Aussage über *jede* Verteilung auf `Bool`, die kein
Spielfeld zeigen kann. Was nicht bei `b` liegt, liegt bei `!b`.
:::

:::proofen
`μ : DiscreteMeasure Bool` is any distribution on `Bool`, and `[Prob μ]` says that its total mass is
one. That is the rule `mass_total μ : μ true + μ false = 1`. So the mass at one side is what the
other side misses to one.

`cases b` (from *Bool*): the point `b` is `false` or `true`, two goals one after the other
(`!false` is `true`: `Bool.not_false`, from *Bool*).

Masses are numbers in $`[0, \infty]` (`ℝ≥0∞`); taking away is allowed when what is taken away is
finite: `ENNReal.add_sub_cancel_left (h : a ≠ ⊤) : a + b - a = b`, and `mass_ne_top : μ b ≠ ⊤` says
that a mass is finite. `rw [← mass_total μ]` rewrites from right to left: the `1` becomes
`μ true + μ false`. At `true`, `μ false` is taken away, and it stands second in the sum:
`add_comm : a + b = b + a` turns the sum round. A rule with a hypothesis can also be used without it:
`rw [ENNReal.add_sub_cancel_left]` then leaves the hypothesis as a second goal, and `exact h` closes a
goal that is exactly `h`.

*Tip.* `cases b`; at `false`: `rw [Bool.not_false, ← mass_total μ]` and
`rw [ENNReal.add_sub_cancel_left mass_ne_top]`; at `true` the same with `Bool.not_true` and
`add_comm` before the last step. Type `\l` for `←`.
:::

:::proofde
`μ : DiscreteMeasure Bool` ist irgendeine Verteilung auf `Bool`, und `[Prob μ]` sagt, dass ihre
Gesamtmasse eins ist. Das ist die Regel `mass_total μ : μ true + μ false = 1`. Also ist die Masse auf
der einen Seite das, was der anderen zu eins fehlt.

`cases b` (aus *Bool*): Der Punkt `b` ist `false` oder `true`, zwei Ziele nacheinander
(`!false` ist `true`: `Bool.not_false`, aus *Bool*).

Massen sind Zahlen in $`[0, \infty]` (`ℝ≥0∞`); wegnehmen darf man, wenn das Weggenommene endlich
ist: `ENNReal.add_sub_cancel_left (h : a ≠ ⊤) : a + b - a = b`, und `mass_ne_top : μ b ≠ ⊤` sagt,
dass eine Masse endlich ist. `rw [← mass_total μ]` schreibt von rechts nach links um: Die `1` wird zu
`μ true + μ false`. Bei `true` wird `μ false` weggenommen, und das steht in der Summe an zweiter
Stelle: `add_comm : a + b = b + a` dreht die Summe um. Eine Regel mit Annahme geht auch ohne sie:
`rw [ENNReal.add_sub_cancel_left]` lässt die Annahme dann als zweites Ziel übrig, und `exact h`
schließt ein Ziel, das genau `h` ist.

*Tipp.* `cases b`; bei `false`: `rw [Bool.not_false, ← mass_total μ]` und
`rw [ENNReal.add_sub_cancel_left mass_ne_top]`; bei `true` dasselbe mit `Bool.not_true` und vor dem
letzten Schritt `add_comm`. `\l` tippen für `←`.
:::
:::solution
```
cases b
rw [Bool.not_false, ← mass_total μ]
rw [ENNReal.add_sub_cancel_left mass_ne_top]
rw [Bool.not_true, ← mass_total μ]
rw [add_comm]
rw [ENNReal.add_sub_cancel_left mass_ne_top]
```
:::
::::

::::leanonly (proof := "(μ ν : DiscreteMeasure Bool) [Prob μ] [Prob ν] (h : μ true = ν ⟦true ‖ true, false⟧) : μ = ν") (lemma := "bool_ext") (new := "ext") (uses := "mass_not, Bool.not_false, Bool.not_true")
:::en
*One bar is enough.* Two distributions on `Bool` with the same mass at `true` are the same. That is
why the board only had to look at one bar.
:::

:::de
*Eine Säule reicht.* Zwei Verteilungen auf `Bool` mit derselben Masse bei `true` sind gleich. Darum
musste das Spielfeld nur auf eine Säule schauen.
:::

:::proofen
Now there is a hypothesis: `h : μ true = ν true`. A new tactic: `ext x`: two distributions are
equal when they have the same mass at every point `x`. Then `cases x` and `exact h` (from *Masses*).
At `false`, your lemma `mass_not` helps, once for `μ` and once for `ν`: `mass_not μ false`.

*Tip.* `ext x`, `cases x`, then `rw [mass_not μ false, mass_not ν false, Bool.not_false, h]`, and
`exact h`.
:::

:::proofde
Jetzt gibt es eine Annahme: `h : μ true = ν true`. Eine neue Taktik: `ext x`: Zwei Verteilungen sind
gleich, wenn sie an jedem Punkt `x` dieselbe Masse haben. Dann `cases x` und `exact h` (aus *Massen*).
Bei `false` hilft dein Lemma `mass_not`, einmal für `μ` und einmal für `ν`: `mass_not μ false`.

*Tipp.* `ext x`, `cases x`, dann `rw [mass_not μ false, mass_not ν false, Bool.not_false, h]`, und
`exact h`.
:::
:::solution
```
ext x
cases x
rw [mass_not μ false, mass_not ν false, Bool.not_false, h]
exact h
```
:::
::::

::::leanonly (proof := "(p : I) : ↑p + ↑(σ p) = (1 : ℝ≥0∞)") (lemma := "add_symm_eq_one") (new := "coin_total") (uses := "coin_true, coin_false, coin_total, mass_total")
:::en
*The coin is whole.* $`p + (1 - p) = 1`: the two masses of the coin add up to one.
:::

:::de
*Die Münze ist ganz.* $`p + (1 - p) = 1`: Die beiden Massen der Münze ergeben zusammen eins.
:::

:::proofen
`coin_total : coin p true + coin p false = 1`. To use it, first write the masses as masses of the coin: your rules `coin_true` and `coin_false`, from right to left. What you prove is unlocked as `add_symm_eq_one`.

*Tip.* `rw [← coin_true, ← coin_false, coin_total]`.
:::

:::proofde
`coin_total : coin p true + coin p false = 1`. Um sie zu benutzen, schreib die Massen zuerst als Massen der Münze: deine Regeln `coin_true` und `coin_false`, von rechts nach links. Was du beweist, wird als `add_symm_eq_one` freigeschaltet.

*Tipp.* `rw [← coin_true, ← coin_false, coin_total]`.
:::
:::solution
```
rw [← coin_true, ← coin_false, coin_total]
```
:::
::::

:::::leanonly (proof := "(b : Bool) : (pure b : DiscreteMeasure Bool) true = bif b then ⟦1 ‖ 0, 1⟧ else ⟦0 ‖ 0, 1⟧") (new := "pure_apply") (lemma := "pure_true") (uses := "pure_apply, beq_true")
:::en
*Surely true.* `pure b` is the distribution that is surely `b`: all its mass lies at `b`. Its mass at
`true` is one if `b` is `true`, else zero.
:::

:::de
*Sicher true.* `pure b` ist die Verteilung, die sicher `b` ist: Ihre ganze Masse liegt bei `b`. Ihre
Masse bei `true` ist eins, wenn `b` gleich `true` ist, sonst null.
:::

::::hint (anchor := "statement")
:::en
`pure b : DiscreteMeasure Bool` is the distribution that puts mass `1` on `b`.
:::

:::de
`pure b : DiscreteMeasure Bool` ist die Verteilung, die Masse `1` auf `b` legt.
:::
::::

::::hint (anchor := "item:pure_apply")
:::en
`rw [pure_apply]` writes the mass of `pure b` at `true` as `bif b == true then 1 else 0`.
:::

:::de
`rw [pure_apply]` schreibt die Masse von `pure b` bei `true` als `bif b == true then 1 else 0`.
:::
::::

:::proofen
By the definition,

```
def pure (a : α) : DiscreteMeasure α := ⟨({a} : Set α).indicator 1⟩
```

the mass is `1` on the set `{a}` and `0` outside it. The game writes this as the new rule
`pure_apply : (pure a) b = bif a == b then 1 else 0`. Then `b == true` is `b` (`beq_true`, from
*Masses*). What you prove is unlocked as `pure_true`.

*Tip.* `rw [pure_apply, beq_true]`.
:::

:::proofde
Nach der Definition,

```
def pure (a : α) : DiscreteMeasure α := ⟨({a} : Set α).indicator 1⟩
```

ist die Masse `1` auf der Menge `{a}` und `0` außerhalb. Das Spiel schreibt das als die neue Regel
`pure_apply : (pure a) b = bif a == b then 1 else 0`. Dann ist `b == true` gleich `b` (`beq_true`,
aus *Massen*). Was du beweist, wird als `pure_true` freigeschaltet.

*Tipp.* `rw [pure_apply, beq_true]`.
:::
:::solution
```
rw [pure_apply, beq_true]
```
:::
:::::

::::circuit (height := "440") (inputs := "x") (gates := "not, alwaysT") (coins := "p") (target := "pure true") (context := "Lean/Rules.lean") (proof := "(p : I) (b : Bool) : (coin p).map (fun _ => b) = ⟦pure b ‖ pure b, coin p, pure true⟧") (lemma := "coin_const") (play := "a=alwaysT; x>a.0; a>out") (uses := "bool_ext, map_true, pure_true, Bool.cond_false, zero_add, Bool.cond_true, coin_total, add_zero, mul_zero, mass_total, coin_true, coin_false")
:::hint (anchor := "old:not")
:::

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
your lemma `pure_true : (pure b) true = bif b then 1 else 0`. Then `b` has to be known: `cases b`. For
`true`, the rule `coin_total : (coin p) true + (coin p) false = 1` says that the coin has total
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

Vergleiche die Säulen bei `true`: `apply bool_ext`, dann `map_true` und dein Lemma
`pure_true : (pure b) true = bif b then 1 else 0`. Dann muss `b` bekannt sein: `cases b`. Für `true` sagt
die Regel `coin_total : (coin p) true + (coin p) false = 1`, dass die Münze die Gesamtmasse
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

:::::leanonly (proof := "(f : Bool → Bool) (b : Bool) : (pure b : DiscreteMeasure Bool).map f = ⟦pure (f b) ‖ pure b, pure (f b), pure (f (f b))⟧") (lemma := "map_pure") (uses := "bool_ext, map_true, pure_true, pure_apply, Bool.cond_false, Bool.cond_self, zero_add, beq_self_eq_true, Bool.cond_true, Bool.true_beq, add_comm, add_zero, mul_zero, add_assoc")
::::hint (anchor := "gap")
:::en
The sure `b`, moved by `f`: where does all the mass lie then?
:::

:::de
Das sichere `b`, von `f` bewegt: Wo liegt dann die ganze Masse?
:::
::::

:::en
*A sure thing, moved.* A move applied to a sure value.
:::

:::de
*Eine sichere Sache, bewegt.* Ein Zug, angewandt auf einen sicheren Wert.
:::

:::proofen
Compare the bars at `true`: `apply bool_ext`, then `map_true`, `pure_true` and, for the mass of
`pure b` at `false`, `pure_apply`. Then `cases b`. What `f` does stays unknown, but where both
branches of a `bif` are equal, `Bool.cond_self` (from *Bool*) helps; `beq_self_eq_true` and
`Bool.true_beq` (from *Masses*) compute the tests `==`. You prove it on `Bool`; it holds for every type,
and it is unlocked as `map_pure` in this general form.

*Tip.* `apply bool_ext`, `rw [map_true, pure_true, pure_true, pure_apply]`, `cases b`, then
`rw [Bool.cond_false, Bool.cond_self, zero_add, beq_self_eq_true, Bool.cond_true]` and
`rw [Bool.cond_true, Bool.true_beq, Bool.cond_false, Bool.cond_self, add_comm, zero_add]`.
:::

:::proofde
Vergleiche die Säulen bei `true`: `apply bool_ext`, dann `map_true`, `pure_true` und, für die Masse von
`pure b` bei `false`, `pure_apply`. Dann `cases b`. Was `f` tut, bleibt unbekannt, aber wo beide Zweige
eines `bif` gleich sind, hilft `Bool.cond_self` (aus *Bool*); `beq_self_eq_true` und
`Bool.true_beq` (aus *Massen*) rechnen die Tests `==` aus. Du beweist es auf `Bool`; es gilt für jeden
Typ und wird in dieser allgemeinen Form als `map_pure` freigeschaltet.

*Tipp.* `apply bool_ext`, `rw [map_true, pure_true, pure_true, pure_apply]`, `cases b`, dann
`rw [Bool.cond_false, Bool.cond_self, zero_add, beq_self_eq_true, Bool.cond_true]` und
`rw [Bool.cond_true, Bool.true_beq, Bool.cond_false, Bool.cond_self, add_comm, zero_add]`.
:::
:::solution
```
apply bool_ext
rw [map_true, pure_true, pure_true, pure_apply]
cases b
rw [Bool.cond_false, Bool.cond_self, zero_add, beq_self_eq_true, Bool.cond_true]
rw [Bool.cond_true, Bool.true_beq, Bool.cond_false, Bool.cond_self, add_comm, zero_add]
```
:::
:::::

::::circuit (height := "540") (inputs := "x") (gates := "not, alwaysT") (coins := "p") (target := "pure false") (context := "Lean/Rules.lean") (proof := "(p : I) : ((coin p).map (fun _ => true)).map not = pure false") (play := "a=alwaysT; b=not; x>a.0; a>b.0; b>out") (uses := "coin_const, map_pure")
:::hint (anchor := "none")
:::

:::en
*Surely `false`, but there is no “always `false`”.* Two gates one after the other: the image measure of
the image measure is the image measure of the composition, $`(P \circ f^{-1}) \circ g^{-1} = P \circ (g \circ f)^{-1}`.
:::

:::de
*Sicher `false`, aber es gibt kein „immer `false`“.* Zwei Bausteine nacheinander: Das Bildmaß des Bildmaßes ist
das Bildmaß der Verkettung, $`(P \circ f^{-1}) \circ g^{-1} = P \circ (g \circ f)^{-1}`.
:::

:::proofen
Your lemma `map_pure : (pure a).map f = pure (f a)`: a gate on a point mass moves the point. Then
`rfl` from *Bool*: the two sides are the same after computing, `!true` is `false`.

*Tip.* `rw [coin_const]`, then `rw [map_pure]` (or both at once: `rw [coin_const, map_pure]`), then
`rfl`.
:::

:::proofde
Dein Lemma `map_pure : (pure a).map f = pure (f a)`: Ein Baustein auf einer Punktmasse verschiebt
den Punkt. Dann `rfl` aus *Bool*: Beide Seiten sind nach Ausrechnen gleich, `!true` ist `false`.

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

:::::leanonly (proof := "(p : I) : (coin p).map not = coin ⟦σ p ‖ p, σ p⟧") (lemma := "coin_not") (uses := "bool_ext, map_true, Bool.not_true, Bool.not_false, Bool.cond_false, Bool.cond_true, zero_add, coin_false, coin_true, add_zero, mul_zero, coin_total")
::::hint (anchor := "gap")
:::en
Flip the coin `p`: what is its mass at `true` now?
:::

:::de
Dreh die Münze `p` um: Was ist jetzt ihre Masse bei `true`?
:::
::::

:::en
*The boss: flip the coin.* Not just the mass at `true`: the whole coin.
:::

:::de
*Der Endgegner: Dreh die Münze um.* Nicht nur die Masse bei `true`: die ganze Münze.
:::

:::proofen
Flipping turns the coin `p` into the coin $`1 - p`: the whole coin, not only its mass at `true`.
Everything of this world comes together: two distributions on `Bool` are the same when their masses
at `true` are (`bool_ext`, your lemma), and the mass at `true` of the flipped coin you computed in
*Where does the mass go?*. Your result becomes the lemma `coin_not`, which the next worlds use all
the time.

*Tip.* `apply bool_ext`, then the computation of *Where does the mass go?* (*Masses*), and at the end `coin_true`.
:::

:::proofde
Umdrehen macht aus der Münze $`p` die Münze $`1 - p`: die ganze Münze, nicht nur ihre Masse bei
`true`. Alles aus dieser Welt kommt zusammen: Zwei Verteilungen auf `Bool` sind gleich, wenn ihre
Massen bei `true` gleich sind (`bool_ext`, dein Lemma), und die Masse bei `true` der umgedrehten Münze
hast du in *Wohin geht die Masse?* ausgerechnet. Dein Ergebnis wird das Lemma `coin_not`, das die
nächsten Welten ständig benutzen.

*Tipp.* `apply bool_ext`, dann die Rechnung aus *Wohin geht die Masse?* (*Massen*), und am Ende `coin_true`.
:::
:::solution
```
apply bool_ext
rw [map_true]
rw [Bool.not_true, Bool.not_false]
rw [Bool.cond_false, Bool.cond_true, zero_add]
rw [coin_false, coin_true]
```
:::
:::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] (p : I) (h : μ true = p) : μ = coin ⟦p ‖ p, σ p⟧") (lemma := "eq_coin") (uses := "bool_ext, coin_true, coin_false, coin_total")
:::hint (anchor := "none")
:::

:::en
*Every distribution is a coin.* A distribution on `Bool` with mass `p` at `true` is the coin `p`.
So the coins are all there is on `Bool`.
:::

:::de
*Jede Verteilung ist eine Münze.* Eine Verteilung auf `Bool` mit Masse `p` bei `true` ist die Münze
`p`. Mehr als Münzen gibt es auf `Bool` also nicht.
:::

:::proofen
Again `apply bool_ext`: the masses at `true` decide. Then `coin_true` and the hypothesis `h`.

*Tip.* `apply bool_ext`, then `rw [coin_true, h]`.
:::

:::proofde
Wieder `apply bool_ext`: Die Massen bei `true` entscheiden. Dann `coin_true` und die Annahme `h`.

*Tipp.* `apply bool_ext`, dann `rw [coin_true, h]`.
:::
:::solution
```
apply bool_ext
rw [coin_true, h]
```
:::
::::
