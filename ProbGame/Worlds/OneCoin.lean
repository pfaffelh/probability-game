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

::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] (h : μ true = 0) : μ false = ⟦1 ‖ 0, 1⟧") (uses := "mass_total, zero_add, coin_total, add_zero, mul_zero, rw")
:::hint (anchor := "none")
:::

:::en
*The whole mass.* A distribution has the total mass one. If nothing lies at `true`, everything lies at `false`.
:::

:::de
*Die ganze Masse.* Eine Verteilung hat die Gesamtmasse eins. Liegt bei `true` nichts, liegt alles bei `false`.
:::

:::proofen
`μ : DiscreteMeasure Bool` is any distribution on `Bool`, and `[Prob μ]` says that its total mass is
one: your theorem `mass_total μ : μ true + μ false = 1`. `h : μ true = 0` is a hypothesis: a rule of
this level only, used like every rule.
:::

:::proofde
`μ : DiscreteMeasure Bool` ist irgendeine Verteilung auf `Bool`, und `[Prob μ]` sagt, dass ihre
Gesamtmasse eins ist: dein Satz `mass_total μ : μ true + μ false = 1`. `h : μ true = 0` ist eine
Annahme: eine Regel nur dieses Levels, benutzt wie jede Regel.
:::
:::solution
```
rw [← mass_total μ, h, zero_add]
```
:::
:::solution
```
rw [← zero_add (μ false), ← h, mass_total]
```
:::
::::

:::::leanonly (proof := "(a b : ℝ≥0∞) : ⟦a - a + b ‖ a + b - a, b - a + a, a - a + b⟧ = b") (new := "tsub_self, tsub_zero") (uses := "tsub_self, zero_add, add_zero, mul_zero, exact, rw")
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

::::hint (anchor := "wrong:a + b - a")
:::en
This does not hold for all `a b`: try `a = ∞`.
:::

:::de
Das gilt nicht für alle `a b`: Probier `a = ∞`.
:::
::::

::::hint (anchor := "wrong:b - a + a")
:::en
This does not hold for all `a b`: try `b < a`.
:::

:::de
Das gilt nicht für alle `a b`: Probier `b < a`.
:::
::::

:::proofen
`tsub_self : a - a = 0` holds for every `a`, also for `a = ∞`. (For a finite `a` also
`a + b - a = b`: the rule `ENNReal.add_sub_cancel_left`, in *The rest of the mass*.)
:::

:::proofde
`tsub_self : a - a = 0` gilt für jedes `a`, auch für `a = ∞`. (Für ein endliches `a` gilt auch
`a + b - a = b`: die Regel `ENNReal.add_sub_cancel_left`, in *Der Rest der Masse*.)
:::
:::solution
```
rw [tsub_self, zero_add]
```
:::
:::solution
```
rw [tsub_self]
exact zero_add b
```
:::
:::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] : μ false + μ true = 1") (uses := "add_comm, mass_total, Prob.total, tsum_bool, add_assoc, coin_total, exact, rw")
:::en
*The other way round.* The total mass, with the summands swapped.
:::

:::de
*Andersherum.* Die Gesamtmasse, mit vertauschten Summanden.
:::

:::proofen
A sum is turned round by `add_comm : a + b = b + a` (from *Masses*).
:::

:::proofde
Eine Summe dreht `add_comm : a + b = b + a` um (aus *Massen*).
:::
:::solution
```
rw [add_comm, mass_total μ]
```
:::
:::solution
```
rw [add_comm]
exact mass_total μ
```
:::
:::solution
```
rw [← mass_total μ, add_comm]
```
:::
:::solution
```
rw [← Prob.total μ, tsum_bool]
```
:::
::::

::::leanonly (proof := "(a : ℝ≥0∞) : a + 0 = ⟦a ‖ a, 0⟧") (lemma := "add_zero") (uses := "add_comm, zero_add, add_assoc, add_zero, mul_zero, exact, rw")
:::en
*Zero on the right.* You have `zero_add : 0 + a = a`, with the zero on the left. Here it stands on
the right.
:::

:::de
*Null rechts.* Du hast `zero_add : 0 + a = a`, mit der Null links. Hier steht sie rechts.
:::

:::proofen
Your result becomes the lemma `add_zero`.
:::

:::proofde
Dein Ergebnis wird das Lemma `add_zero`.
:::
:::solution
```
rw [add_comm, zero_add]
```
:::
:::solution
```
rw [add_comm]
rw [zero_add]
```
:::
:::solution
```
rw [add_comm]
exact zero_add a
```
:::
::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] (b : Bool) : μ b = ⟦1 - μ (!b) ‖ 1 - μ (!b), μ (!b) - 1, 1 - μ b⟧") (lemma := "mass_not") (new := "ENNReal.add_sub_cancel_left") (uses := "Bool.not_false, mass_total, ENNReal.add_sub_cancel_left, mass_ne_top, Bool.not_true, add_comm, coin_total, add_assoc, cases, exact, rw")
:::en
*The rest of the mass.* Now in Lean only: a statement about *every* distribution on `Bool`, which no
board can show. What is not at `b` lies at `!b`.
:::

:::de
*Der Rest der Masse.* Jetzt nur in Lean: eine Aussage über *jede* Verteilung auf `Bool`, die kein
Spielfeld zeigen kann. Was nicht bei `b` liegt, liegt bei `!b`.
:::

:::proofen
`mass_total μ : μ true + μ false = 1`: the mass at one side is what the other side misses to one.
The point `b` is `false` or `true`.

Masses are numbers in $`[0, \infty]` (`ℝ≥0∞`); taking away is allowed when what is taken away is
finite: `ENNReal.add_sub_cancel_left (h : a ≠ ⊤) : a + b - a = b`, and `mass_ne_top : μ b ≠ ⊤` says
that a mass is finite. The hypothesis is written behind the rule; without it, `rw` leaves it as a
second goal.
:::

:::proofde
`mass_total μ : μ true + μ false = 1`: Die Masse auf der einen Seite ist das, was der anderen zu
eins fehlt. Der Punkt `b` ist `false` oder `true`.

Massen sind Zahlen in $`[0, \infty]` (`ℝ≥0∞`); wegnehmen darf man, wenn das Weggenommene endlich
ist: `ENNReal.add_sub_cancel_left (h : a ≠ ⊤) : a + b - a = b`, und `mass_ne_top : μ b ≠ ⊤` sagt,
dass eine Masse endlich ist. Die Annahme schreibt man hinter die Regel; ohne sie lässt `rw` sie als
zweites Ziel übrig.
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
:::solution
```
rw [← mass_total μ]
cases b
rw [Bool.not_false, ENNReal.add_sub_cancel_left mass_ne_top]
rw [Bool.not_true, add_comm, ENNReal.add_sub_cancel_left mass_ne_top]
```
:::
:::solution
```
cases b
rw [Bool.not_false]
rw [← mass_total μ]
rw [ENNReal.add_sub_cancel_left]
exact mass_ne_top
rw [Bool.not_true]
rw [← mass_total μ]
rw [add_comm]
rw [ENNReal.add_sub_cancel_left]
exact mass_ne_top
```
:::
::::

::::leanonly (proof := "(μ ν : DiscreteMeasure Bool) [Prob μ] [Prob ν] (h : μ true = ν ⟦true ‖ true, false⟧) : μ = ν") (lemma := "bool_ext") (new := "ext") (uses := "mass_not, Bool.not_false, Bool.not_true, cases, exact, ext, rw")
:::en
*One bar is enough.* Two distributions on `Bool` with the same mass at `true` are the same. That is
why the board only had to look at one bar.
:::

:::de
*Eine Säule reicht.* Zwei Verteilungen auf `Bool` mit derselben Masse bei `true` sind gleich. Darum
musste das Spielfeld nur auf eine Säule schauen.
:::

:::proofen
Now there is a hypothesis: `h : μ true = ν true`. A new tactic: `ext x`: two distributions are equal
when they have the same mass at every point `x`. At `false`, your lemma `mass_not` helps, once for
`μ` and once for `ν`: `mass_not μ false`.
:::

:::proofde
Jetzt gibt es eine Annahme: `h : μ true = ν true`. Eine neue Taktik: `ext x`: Zwei Verteilungen sind
gleich, wenn sie an jedem Punkt `x` dieselbe Masse haben. Bei `false` hilft dein Lemma `mass_not`,
einmal für `μ` und einmal für `ν`: `mass_not μ false`.
:::
:::solution
```
ext x
cases x
rw [mass_not μ false, mass_not ν false, Bool.not_false, h]
exact h
```
:::
:::solution
```
ext x
cases x
rw [mass_not μ false, mass_not ν false, Bool.not_false, h]
rw [h]
```
:::
::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] (p : I) (h : μ true = p) : μ = coin ⟦p ‖ p, σ p⟧") (lemma := "eq_coin") (uses := "bool_ext, coin_true, coin_false, coin_total, apply, exact, rfl, rw")
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
Your lemma `bool_ext` says: `μ = ν`, if `μ true = ν true`. The goal here is `μ = coin p`, an
equation of two distributions on `Bool`: `apply` (from *Masses*) uses the lemma from its end.
:::

:::proofde
Dein Lemma `bool_ext` sagt: `μ = ν`, wenn `μ true = ν true`. Das Ziel hier ist `μ = coin p`, eine
Gleichung zweier Verteilungen auf `Bool`: `apply` (aus *Massen*) benutzt das Lemma von seinem Ende
her.
:::
:::solution
```
apply bool_ext
rw [coin_true, h]
```
:::
:::solution
```
apply bool_ext
rw [coin_true]
exact h
```
:::
:::solution
```
apply bool_ext
rw [h]
rfl
```
:::
:::solution
```
exact bool_ext μ (coin p) h
```
:::
::::

:::::leanonly (proof := "(b : Bool) : (pure b : DiscreteMeasure Bool) true = bif b then ⟦1 ‖ 0, 1⟧ else ⟦0 ‖ 0, 1⟧") (new := "pure_apply") (lemma := "pure_true") (uses := "pure_apply, beq_true, <;>, cases, rfl, rw")
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
`pure_apply : (pure a) b = bif a == b then 1 else 0`.  What you prove is unlocked as `pure_true`.
:::

:::proofde
Nach der Definition,

```
def pure (a : α) : DiscreteMeasure α := ⟨({a} : Set α).indicator 1⟩
```

ist die Masse `1` auf der Menge `{a}` und `0` außerhalb. Das Spiel schreibt das als die neue Regel
`pure_apply : (pure a) b = bif a == b then 1 else 0`.  Was du beweist, wird als `pure_true` freigeschaltet.
:::
:::solution
```
rw [pure_apply, beq_true]
```
:::
:::solution
```
rw [pure_apply]
cases b <;> rfl
```
:::
:::::

::::circuit (height := "440") (inputs := "x") (gates := "not, alwaysT") (coins := "p") (target := "pure true") (context := "Lean/Rules.lean") (proof := "(p : I) (b : Bool) : (coin p).map (fun _ => b) = pure b") (lemma := "coin_const") (play := "a=alwaysT; x>a.0; a>out") (uses := "bool_ext, map_true, pure_true, Bool.cond_false, zero_add, Bool.cond_true, coin_total, mass_total, add_zero, mul_zero, coin_true, coin_false, apply, cases, rw")
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
`pure b` is the point mass at `b`, and `fun _ => b` is the constant map. The statement says what the
board showed, for both values `b`: all the mass goes to one point. It becomes your lemma
`coin_const`.

Compare the bars at `true`, as for `eq_coin`. `rw [Bool.cond_true]` rewrites one `bif` at a time.
:::

:::proofde
`pure b` ist die Punktmasse in `b`, und `fun _ => b` ist die konstante Abbildung. Die Aussage sagt,
was das Spielfeld gezeigt hat, für beide Werte `b`: Die ganze Masse geht zu einem Punkt. Sie wird
dein Lemma `coin_const`.

Vergleiche die Säulen bei `true`, wie bei `eq_coin`. `rw [Bool.cond_true]` schreibt immer nur ein
`bif` um.
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
:::solution
```
cases b
apply bool_ext
rw [map_true, pure_true, Bool.cond_false, Bool.cond_false, Bool.cond_false, zero_add]
apply bool_ext
rw [map_true, pure_true, Bool.cond_true, Bool.cond_true, Bool.cond_true, coin_total]
```
:::
:::solution
```
apply bool_ext
rw [map_true, pure_true]
cases b
rw [Bool.cond_false, Bool.cond_false, Bool.cond_false, zero_add]
rw [Bool.cond_true, Bool.cond_true, Bool.cond_true, mass_total]
```
:::
::::

:::::leanonly (proof := "(b : Bool) : (pure b : DiscreteMeasure Bool) false = bif b then ⟦0 ‖ 0, 1⟧ else ⟦1 ‖ 0, 1⟧") (lemma := "pure_false") (uses := "pure_apply, beq_self_eq_true, Bool.cond_true, Bool.cond_false, Bool.true_beq, mass_not, Bool.not_false, pure_true, tsub_zero, tsub_self, Bool.not_true, <;>, cases, rfl, rw")
::::hint (anchor := "gap")
:::en
All the mass of `pure b` lies at `b`: how much of it lies at `false`?
:::

:::de
Die ganze Masse von `pure b` liegt bei `b`: Wie viel davon liegt bei `false`?
:::
::::

:::en
*Surely not false.* The mass of `pure b` at `false`: the counterpart of `pure_true`.
:::

:::de
*Sicher nicht false.* Die Masse von `pure b` bei `false`: das Gegenstück zu `pure_true`.
:::

:::proofen
The counterpart of `pure_true`, from the same rule. What you prove is unlocked as `pure_false`.
:::

:::proofde
Das Gegenstück zu `pure_true`, aus derselben Regel. Was du beweist, wird als `pure_false`
freigeschaltet.
:::
:::solution
```
rw [pure_apply]
cases b <;> rfl
```
:::
:::solution
```
rw [pure_apply]
cases b
rfl
rfl
```
:::
:::solution
```
rw [pure_apply]
cases b
rw [beq_self_eq_true, Bool.cond_true, Bool.cond_false]
rw [Bool.true_beq, Bool.cond_false, Bool.cond_true]
```
:::
:::solution
```
rw [mass_not (pure b) false, Bool.not_false, pure_true]
cases b
rw [Bool.cond_false, Bool.cond_false, tsub_zero]
rw [Bool.cond_true, Bool.cond_true, tsub_self]
```
:::
:::::

::::leanonly (proof := ": (pure true : DiscreteMeasure Bool) true = ⟦1 ‖ 0, 1⟧ ∧ (pure true : DiscreteMeasure Bool) false = ⟦0 ‖ 0, 1⟧") (uses := "pure_true, Bool.cond_true, pure_false, pure_apply, Bool.cond_false, constructor, rfl, rw")
:::en
*Surely `true`.* Both masses of `pure true`, in one statement.
:::

:::de
*Sicher `true`.* Beide Massen von `pure true`, in einer Aussage.
:::

:::proofen
Two statements with `∧`, as in *Masses*; for each you have a lemma.
:::

:::proofde
Zwei Aussagen mit `∧`, wie in *Massen*; für jede hast du ein Lemma.
:::
:::solution
```
constructor
rw [pure_true, Bool.cond_true]
rw [pure_false, Bool.cond_true]
```
:::
:::solution
```
constructor
rw [pure_true]
rfl
rw [pure_false]
rfl
```
:::
:::solution
```
constructor
rw [pure_apply]
rfl
rw [pure_apply]
rfl
```
:::
::::

:::::leanonly (proof := "(f : Bool → Bool) (b : Bool) : (pure b : DiscreteMeasure Bool).map f = ⟦pure (f b) ‖ pure b, pure (f b), pure (f (f b))⟧") (lemma := "map_pure") (uses := "bool_ext, map_true, pure_true, pure_false, Bool.cond_false, Bool.cond_self, zero_add, Bool.cond_true, add_comm, add_zero, mul_zero, add_assoc, apply, cases, rw")
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
Compare the bars at `true`. What `f` does stays unknown, but where both branches of a `bif` are
equal, `Bool.cond_self` (from *Bool*) helps. You prove it on `Bool`; it holds for every type, and it
is unlocked as `map_pure` in this general form.
:::

:::proofde
Vergleiche die Säulen bei `true`. Was `f` tut, bleibt unbekannt, aber wo beide Zweige eines `bif`
gleich sind, hilft `Bool.cond_self` (aus *Bool*). Du beweist es auf `Bool`; es gilt für jeden Typ
und wird in dieser allgemeinen Form als `map_pure` freigeschaltet.
:::
:::solution
```
apply bool_ext
rw [map_true, pure_true, pure_true, pure_false]
cases b
rw [Bool.cond_false, Bool.cond_false, Bool.cond_self, zero_add]
rw [Bool.cond_true, Bool.cond_true, Bool.cond_self, add_comm, zero_add]
```
:::
:::solution
```
cases b
apply bool_ext
rw [map_true, pure_true, pure_false, pure_true, Bool.cond_false, Bool.cond_false, Bool.cond_self, zero_add]
apply bool_ext
rw [map_true, pure_true, pure_false, pure_true, Bool.cond_true, Bool.cond_true, Bool.cond_self, add_comm, zero_add]
```
:::
:::solution
```
apply bool_ext
rw [map_true, pure_true, pure_true, pure_false]
cases b
rw [Bool.cond_false, Bool.cond_false, Bool.cond_self, zero_add]
rw [Bool.cond_true, Bool.cond_true, Bool.cond_self, add_zero]
```
:::
:::::

::::circuit (height := "540") (inputs := "x") (gates := "not, alwaysT") (coins := "p") (target := "pure false") (context := "Lean/Rules.lean") (proof := "(p : I) : ((coin p).map (fun _ => true)).map not = pure false") (play := "a=alwaysT; b=not; x>a.0; a>b.0; b>out") (uses := "coin_const, map_pure, Bool.not_true, bool_ext, pure_true, Bool.not_false, apply, rfl, rw")
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
Your lemma `map_pure : (pure a).map f = pure (f a)`: a gate on a point mass moves the point.
:::

:::proofde
Dein Lemma `map_pure : (pure a).map f = pure (f a)`: Ein Baustein auf einer Punktmasse verschiebt
den Punkt.
:::
:::solution
```
rw [coin_const]
rw [map_pure]
rfl
```
:::
:::solution
```
rw [coin_const, map_pure, Bool.not_true]
```
:::
:::solution
```
apply bool_ext
rw [coin_const, map_pure, pure_true, pure_true, Bool.not_true]
```
:::
::::

:::::leanonly (proof := "(p : I) : (coin p).map not = coin ⟦σ p ‖ p, σ p⟧") (lemma := "coin_not") (uses := "bool_ext, map_true, Bool.not_true, Bool.not_false, Bool.cond_false, Bool.cond_true, zero_add, coin_false, coin_true, eq_coin, coin_not_true, add_zero, mul_zero, coin_total, apply, exact, rw")
::::hint (anchor := "gap")
:::en
Flip the coin `p`: what is its mass at `true` now?
:::

:::de
Dreh die Münze `p` um: Was ist jetzt ihre Masse bei `true`?
:::
::::

:::en
*Boss: flip the coin.* Not just the mass at `true`: the whole coin.
:::

:::de
*Endgegner: Dreh die Münze um.* Nicht nur die Masse bei `true`: die ganze Münze.
:::

:::proofen
Flipping turns the coin `p` into the coin $`1 - p`: the whole coin, not only its mass at `true`.
Your result becomes the lemma `coin_not`, which the next worlds use all the time.
:::

:::proofde
Umdrehen macht aus der Münze $`p` die Münze $`1 - p`: die ganze Münze, nicht nur ihre Masse bei
`true`. Dein Ergebnis wird das Lemma `coin_not`, das die nächsten Welten ständig benutzen.
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
:::solution
```
apply eq_coin
rw [map_true, Bool.not_true, Bool.not_false, Bool.cond_false, Bool.cond_true, zero_add, coin_false]
```
:::
:::solution
```
apply eq_coin
exact coin_not_true p
```
:::
:::solution
```
apply bool_ext
rw [coin_not_true, coin_true]
```
:::
:::::
