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
example $`p` (the slider changes it).
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
Spielfeld die Säulen für ein Beispiel-$`p` (der Schieberegler ändert es).
:::

::::circuit (height := "440") (inputs := "x") (gates := "not") (coins := "p") (target := "bool true:1-p false:p") (context := "Lean/Rules.lean") (proof := "(p : I) : (not <$> coin p) true = σ p") (play := "a=not; x>a.0; a>out") (uses := "map_true, Bool.not_true, Bool.not_false, Bool.cond_false, Bool.cond_true, zero_add, coin_false, add_zero, mul_zero, coin_true")
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
*Now the proof.* Everything it needs you know from *Circuits* and *Masses*: `coin p` and its masses, `f <$> μ`, and
the rules. First the rule of the gates, `map_true`; then computing, one rule after another:
`Bool.not_true`, `Bool.not_false`, `Bool.cond_false`, `Bool.cond_true`, `zero_add` and `coin_false`.
Keep this computation in mind: the boss of this world needs it again.

*Tip.* `rw [map_true]`, `rw [Bool.not_true, Bool.not_false]`,
`rw [Bool.cond_false, Bool.cond_true, zero_add]`, `rw [coin_false]` (type it, or tap the inventory,
and press *Run*).
:::

:::proofde
*Jetzt der Beweis.* Alles, was er braucht, kennst du aus *Schaltungen* und *Massen*: `coin p` und seine Massen,
`f <$> μ` und die Regeln. Zuerst die Regel der Bausteine, `map_true`; dann Rechnen, eine Regel nach der
anderen: `Bool.not_true`, `Bool.not_false`, `Bool.cond_false`, `Bool.cond_true`, `zero_add` und
`coin_false`. Merk dir diese Rechnung: Der Endgegner dieser Welt braucht sie noch einmal.

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

::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] (h : μ true = 0) : μ false = 1") (new := "mass_total") (uses := "mass_total, zero_add, coin_total, add_zero, mul_zero")
:::en
*The whole mass.* A distribution has the total mass one. If nothing lies at `true`, everything lies at `false`.
:::

:::de
*Die ganze Masse.* Eine Verteilung hat die Gesamtmasse eins. Liegt bei `true` nichts, liegt alles bei `false`.
:::

:::proofen
`μ : DiscreteMeasure Bool` is any distribution on `Bool`, and `[Prob μ]` says that its total mass is one: the rule `mass_total μ : μ true + μ false = 1`. `h : μ true = 0` is a hypothesis, a rule of this level only. `rw [← mass_total μ]` rewrites from right to left: the `1` becomes `μ true + μ false`. Then `h`, then `zero_add`.

*Tip.* `rw [← mass_total μ, h, zero_add]` (type `\l` for `←`, or tap ←).
:::

:::proofde
`μ : DiscreteMeasure Bool` ist irgendeine Verteilung auf `Bool`, und `[Prob μ]` sagt, dass ihre Gesamtmasse eins ist: die Regel `mass_total μ : μ true + μ false = 1`. `h : μ true = 0` ist eine Annahme, eine Regel nur dieses Levels. `rw [← mass_total μ]` schreibt von rechts nach links um: Die `1` wird zu `μ true + μ false`. Dann `h`, dann `zero_add`.

*Tipp.* `rw [← mass_total μ, h, zero_add]` (`\l` tippen für `←`, oder ← antippen).
:::
:::solution
```
rw [← mass_total μ, h, zero_add]
```
:::
::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] : μ true ≠ ⊤") (new := "mass_ne_top, exact") (uses := "mass_ne_top")
:::en
*Finite.* Masses are numbers in $`[0, \infty]`; the mass of a distribution is finite, `≠ ⊤` (`⊤` is $`\infty`).
:::

:::de
*Endlich.* Massen sind Zahlen in $`[0, \infty]`; die Masse einer Verteilung ist endlich, `≠ ⊤` (`⊤` ist $`\infty`).
:::

:::proofen
The rule `mass_ne_top : μ b ≠ ⊤` is exactly the goal. `exact h` closes a goal that is exactly `h`.

*Tip.* `exact mass_ne_top`.
:::

:::proofde
Die Regel `mass_ne_top : μ b ≠ ⊤` ist genau das Ziel. `exact h` schließt ein Ziel, das genau `h` ist.

*Tipp.* `exact mass_ne_top`.
:::
:::solution
```
exact mass_ne_top
```
:::
::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] : μ true + μ false - μ true = μ false") (new := "ENNReal.add_sub_cancel_left") (uses := "ENNReal.add_sub_cancel_left, mass_ne_top")
:::en
*Taking away.* What is added and taken away again is gone, when it is finite.
:::

:::de
*Wegnehmen.* Was dazukommt und wieder weggenommen wird, ist weg, wenn es endlich ist.
:::

:::proofen
`ENNReal.add_sub_cancel_left (h : a ≠ ⊤) : a + b - a = b` (in $`[0, \infty]`, $`\infty - \infty` would make no sense, hence `h`). A rule with a hypothesis gets it in the brackets: here `mass_ne_top`.

*Tip.* `rw [ENNReal.add_sub_cancel_left mass_ne_top]`.
:::

:::proofde
`ENNReal.add_sub_cancel_left (h : a ≠ ⊤) : a + b - a = b` (in $`[0, \infty]` ergäbe $`\infty - \infty` keinen Sinn, daher `h`). Eine Regel mit Annahme bekommt sie in die Klammer: hier `mass_ne_top`.

*Tipp.* `rw [ENNReal.add_sub_cancel_left mass_ne_top]`.
:::
:::solution
```
rw [ENNReal.add_sub_cancel_left mass_ne_top]
```
:::
::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] : μ false + μ true = 1") (new := "add_comm") (uses := "add_comm, mass_total, add_assoc, coin_total")
:::en
*The other way round.* The total mass, with the summands swapped.
:::

:::de
*Andersherum.* Die Gesamtmasse, mit vertauschten Summanden.
:::

:::proofen
`add_comm : a + b = b + a` turns a sum round; then it is `mass_total μ`.

*Tip.* `rw [add_comm, mass_total μ]`.
:::

:::proofde
`add_comm : a + b = b + a` dreht eine Summe um; dann ist es `mass_total μ`.

*Tipp.* `rw [add_comm, mass_total μ]`.
:::
:::solution
```
rw [add_comm, mass_total μ]
```
:::
::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] (b : Bool) : μ b = 1 - μ (!b)") (lemma := "mass_not") (uses := "Bool.not_false, mass_total, ENNReal.add_sub_cancel_left, mass_ne_top, Bool.not_true, add_comm, coin_total, add_assoc")
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

`cases b` (from *Circuits*): the point `b` is `false` or `true`, two goals one after the other
(`!false` is `true`: `Bool.not_false`, from *Circuits*).

Masses are numbers in $`[0, \infty]` (`ENNReal`); taking away is allowed when what is taken away is
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

`cases b` (aus *Schaltungen*): Der Punkt `b` ist `false` oder `true`, zwei Ziele nacheinander
(`!false` ist `true`: `Bool.not_false`, aus *Schaltungen*).

Massen sind Zahlen in $`[0, \infty]` (`ENNReal`); wegnehmen darf man, wenn das Weggenommene endlich
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

::::leanonly (proof := "(μ ν : DiscreteMeasure Bool) [Prob μ] [Prob ν] (h : μ true = ν true) : μ = ν") (lemma := "bool_ext") (new := "ext") (uses := "mass_not, Bool.not_false, Bool.not_true")
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
equal when they have the same mass at every point `x`. Then `cases x` and `exact h` (from *Finite*).
At `false`, your lemma `mass_not` helps, once for `μ` and once for `ν`: `mass_not μ false`.

*Tip.* `ext x`, `cases x`, then `rw [mass_not μ false, mass_not ν false, Bool.not_false, h]`, and
`exact h`.
:::

:::proofde
Jetzt gibt es eine Annahme: `h : μ true = ν true`. Eine neue Taktik: `ext x`: Zwei Verteilungen sind
gleich, wenn sie an jedem Punkt `x` dieselbe Masse haben. Dann `cases x` und `exact h` (aus *Endlich*).
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

::::leanonly (proof := "(p : I) : ↑p + ↑(σ p) = (1 : ENNReal)") (new := "coin_total") (uses := "coin_true, coin_false, coin_total, mass_total")
:::en
*The coin is whole.* $`p + (1 - p) = 1`: the two masses of the coin add up to one.
:::

:::de
*Die Münze ist ganz.* $`p + (1 - p) = 1`: Die beiden Massen der Münze ergeben zusammen eins.
:::

:::proofen
`coin_total : coin p true + coin p false = 1`. To use it, first write the masses as masses of the coin: your rules `coin_true` and `coin_false`, from right to left.

*Tip.* `rw [← coin_true, ← coin_false, coin_total]`.
:::

:::proofde
`coin_total : coin p true + coin p false = 1`. Um sie zu benutzen, schreib die Massen zuerst als Massen der Münze: deine Regeln `coin_true` und `coin_false`, von rechts nach links.

*Tipp.* `rw [← coin_true, ← coin_false, coin_total]`.
:::
:::solution
```
rw [← coin_true, ← coin_false, coin_total]
```
:::
::::

::::leanonly (proof := ": (pure true : DiscreteMeasure Bool) true = 1") (new := "pure_true") (uses := "pure_true, Bool.cond_true, Bool.cond_false")
:::en
*Surely true.* `pure b` is the distribution that is surely `b`: all its mass lies at `b`.
:::

:::de
*Sicher true.* `pure b` ist die Verteilung, die sicher `b` ist: Ihre ganze Masse liegt bei `b`.
:::

:::proofen
`pure_true : (pure b) true = bif b then 1 else 0`: one if `b` is `true`, else zero. By the definition,

```
def pure (a : α) : DiscreteMeasure α := ⟨({a} : Set α).indicator 1⟩
```

the mass is `1` on the set `{a}` and `0` outside it.

*Tip.* `rw [pure_true, Bool.cond_true]`.
:::

:::proofde
`pure_true : (pure b) true = bif b then 1 else 0`: eins, wenn `b` gleich `true` ist, sonst null. Nach der Definition,

```
def pure (a : α) : DiscreteMeasure α := ⟨({a} : Set α).indicator 1⟩
```

ist die Masse `1` auf der Menge `{a}` und `0` außerhalb.

*Tipp.* `rw [pure_true, Bool.cond_true]`.
:::
:::solution
```
rw [pure_true, Bool.cond_true]
```
:::
::::

::::circuit (height := "440") (inputs := "x") (gates := "not, alwaysT") (coins := "p") (target := "pure true") (context := "Lean/Rules.lean") (proof := "(p : I) (b : Bool) : (fun _ => b) <$> coin p = pure b") (lemma := "coin_const") (play := "a=alwaysT; x>a.0; a>out") (new := "apply") (uses := "bool_ext, map_true, pure_true, Bool.cond_false, zero_add, Bool.cond_true, coin_total, add_zero, mul_zero, mass_total")
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

::::leanonly (proof := ": (not <$> (pure true : DiscreteMeasure Bool)) = pure false") (new := "map_pure") (uses := "map_pure, Bool.not_true, Bool.not_false")
:::en
*A sure thing, moved.* A move applied to a sure value is the sure value of its image.
:::

:::de
*Eine sichere Sache, bewegt.* Ein Zug, angewandt auf einen sicheren Wert, ist der sichere Wert seines Bildes.
:::

:::proofen
`map_pure : f <$> pure a = pure (f a)`.

*Tip.* `rw [map_pure, Bool.not_true]`.
:::

:::proofde
`map_pure : f <$> pure a = pure (f a)`.

*Tipp.* `rw [map_pure, Bool.not_true]`.
:::
:::solution
```
rw [map_pure, Bool.not_true]
```
:::
::::

::::circuit (height := "540") (inputs := "x") (gates := "not, alwaysT") (coins := "p") (target := "pure false") (context := "Lean/Rules.lean") (proof := "(p : I) : not <$> ((fun _ => true) <$> coin p) = pure false") (play := "a=alwaysT; b=not; x>a.0; a>b.0; b>out") (uses := "coin_const, map_pure")
:::en
*Surely `false`, but there is no “always `false`”.* Two gates one after the other: the image measure of
the image measure is the image measure of the composition, $`(P \circ f^{-1}) \circ g^{-1} = P \circ (g \circ f)^{-1}`.
:::

:::de
*Sicher `false`, aber es gibt kein „immer `false`“.* Zwei Bausteine nacheinander: Das Bildmaß des Bildmaßes ist
das Bildmaß der Verkettung, $`(P \circ f^{-1}) \circ g^{-1} = P \circ (g \circ f)^{-1}`.
:::

:::proofen
A new rule: `map_pure : f <$> pure a = pure (f a)`: a gate on a point mass moves the point. Then
`rfl` from *Circuits*: the two sides are the same after computing, `!true` is `false`.

*Tip.* `rw [coin_const]`, then `rw [map_pure]` (or both at once: `rw [coin_const, map_pure]`), then
`rfl`.
:::

:::proofde
Eine neue Regel: `map_pure : f <$> pure a = pure (f a)`: Ein Baustein auf einer Punktmasse verschiebt
den Punkt. Dann `rfl` aus *Schaltungen*: Beide Seiten sind nach Ausrechnen gleich, `!true` ist `false`.

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

::::circuit (height := "440") (inputs := "x") (gates := "not, alwaysT, alwaysF") (coins := "p") (target := "bernoulli 1-p") (context := "Lean/Rules.lean") (proof := "(p : I) : not <$> coin p = coin (σ p)") (lemma := "coin_not") (play := "a=not; x>a.0; a>out") (uses := "bool_ext, map_true, Bool.not_true, Bool.not_false, Bool.cond_false, Bool.cond_true, zero_add, coin_false, coin_true, add_zero, mul_zero")
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

*Tip.* `apply bool_ext`, then the computation of the first level, and at the end `coin_true`.
:::

:::proofde
Umdrehen macht aus der Münze $`p` die Münze $`1 - p`: die ganze Münze, nicht nur ihre Masse bei
`true`. Alles aus dieser Welt kommt zusammen: Zwei Verteilungen auf `Bool` sind gleich, wenn ihre
Massen bei `true` gleich sind (`bool_ext`, dein Lemma), und die Masse bei `true` der umgedrehten Münze
hast du in *Wohin geht die Masse?* ausgerechnet. Dein Ergebnis wird das Lemma `coin_not`, das die
nächsten Welten ständig benutzen.

*Tipp.* `apply bool_ext`, dann die Rechnung des ersten Levels, und am Ende `coin_true`.
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
::::
