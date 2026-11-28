import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "DiscreteMeasure" =>

%%%
htmlSplit := .never
number := false
%%%

:::en
A distribution on `Bool` is, in Lean, `μ : DiscreteMeasure Bool`: it gives each of the two points its
*mass*, `μ true` and `μ false`, the heights of its two bars. `[Prob μ]` says that the two masses add
up to one. This world proves what holds for every such `μ`; the first example is the sure
distribution `pure b`. The coins come in the next world.
:::

:::de
Eine Verteilung auf `Bool` ist in Lean `μ : DiscreteMeasure Bool`: Sie gibt jedem der beiden Punkte
seine *Masse*, `μ true` und `μ false`, die Höhen ihrer beiden Säulen. `[Prob μ]` sagt, dass die beiden
Massen zusammen eins ergeben. Diese Welt beweist, was für jedes solche `μ` gilt; das erste Beispiel
ist die sichere Verteilung `pure b`. Die Münzen kommen in der nächsten Welt.
:::

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
A distribution is, in Lean, its masses (its *weight* function):

```
structure DiscreteMeasure (α : Type) where
  weight : α → ℝ≥0∞
```

`ℝ≥0∞` (in Lean `ENNReal`) are the numbers from 0 to ∞, ∞ included: a mass is never negative.
(`μ x` is `μ.weight x`.) By the definition of `pure`,

```
def pure (a : α) : DiscreteMeasure α := ⟨({a} : Set α).indicator 1⟩
```

the mass is `1` on the set `{a}` and `0` outside it. The game writes this as the new rule
`pure_apply : (pure a) b = bif a == b then 1 else 0`.  What you prove is unlocked as `pure_true`.
:::

:::proofde
Eine Verteilung ist in Lean ihre Massen (ihre *Gewichtsfunktion*):

```
structure DiscreteMeasure (α : Type) where
  weight : α → ℝ≥0∞
```

`ℝ≥0∞` (in Lean `ENNReal`) sind die Zahlen von 0 bis ∞, ∞ eingeschlossen: Eine Masse ist nie negativ.
(`μ x` ist `μ.weight x`.) Nach der Definition von `pure`,

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

:::::leanonly (proof := "(b : Bool) : (pure b : DiscreteMeasure Bool) false = bif b then ⟦0 ‖ 0, 1⟧ else ⟦1 ‖ 0, 1⟧") (lemma := "pure_false") (uses := "pure_apply, beq_self_eq_true, Bool.cond_true, Bool.cond_false, Bool.true_beq, <;>, cases, rfl, rw")
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
:::::

::::leanonly (proof := "(x y : ℝ≥0∞) : ∑ a, (bif a then x else y) = x + y") (new := "Fintype.sum_bool") (uses := "Fintype.sum_bool, Bool.cond_true, Bool.cond_false, rw, -rfl")
:::en
*A sum over Bool.* A move collects masses: it adds up the masses of all points that go to the same
place. So we need sums. `∑ a, g a` is the sum of `g a` over all points `a` of a finite type; over `Bool`
there are two, and the rule (from Mathlib) is

`Fintype.sum_bool : ∑ a, g a = g true + g false`.
:::

:::de
*Eine Summe über Bool.* Ein Zug sammelt Massen: Er addiert die Massen aller Punkte, die an dieselbe
Stelle gehen. Wir brauchen also Summen. `∑ a, g a` ist die Summe der `g a` über alle Punkte `a` eines
endlichen Typs; über `Bool` sind es zwei, und die Regel (aus Mathlib) ist

`Fintype.sum_bool : ∑ a, g a = g true + g false`.
:::

:::proofen
Here `g a` is `bif a then x else y`.
:::

:::proofde
Hier ist `g a` gleich `bif a then x else y`.
:::
:::solution
```
rw [Fintype.sum_bool, Bool.cond_true, Bool.cond_false]
```
:::
:::solution
```
rw [Fintype.sum_bool, Bool.cond_false, Bool.cond_true]
```
:::
::::

:::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] : μ true + μ false = 1") (lemma := "mass_total") (new := "Prob.total, tsum_bool, add_comm") (uses := "Prob.total, tsum_bool, add_comm, add_assoc, rw")
:::en
*The whole mass.* `[Prob μ]` says: `μ` is a distribution, its masses add up to one. On `Bool` there
are two of them.
:::

:::de
*Die ganze Masse.* `[Prob μ]` sagt: `μ` ist eine Verteilung, ihre Massen ergeben zusammen eins. Auf
`Bool` sind es zwei.
:::

::::hint (anchor := "statement")
:::en
`[Prob μ]` is an assumption about `μ`. The weights sum to 1.
:::

:::de
`[Prob μ]` ist eine Annahme über `μ`. Die Gewichte summieren sich zu 1.
:::
::::

::::hint (anchor := "back")
:::en
New: `←`. `rw [← h]` rewrites from right to left: it puts the left side of `h` where its right side
stands. Tap `←`, or type `\l`.
:::

:::de
Neu: `←`. `rw [← h]` schreibt von rechts nach links um: Es setzt die linke Seite von `h` dorthin, wo
ihre rechte steht. Tippe `←` an, oder tippe `\l`.
:::
::::

:::proofen
`Prob.total μ : ∑' a, μ a = 1` is a sum over all points, `∑'`; read from right to left, it makes the
`1` of the goal this sum. `tsum_bool` writes a sum over `Bool` as its two terms, `false` first;
`add_comm : a + b = b + a` turns them round.
:::

:::proofde
`Prob.total μ : ∑' a, μ a = 1` ist eine Summe über alle Punkte, `∑'`; von rechts nach links gelesen
macht sie die `1` des Ziels zu dieser Summe. `tsum_bool` schreibt eine Summe über `Bool` als ihre
zwei Summanden, `false` zuerst; `add_comm : a + b = b + a` dreht sie um.
:::
:::solution
```
rw [← Prob.total μ, tsum_bool, add_comm]
```
:::
:::solution
```
rw [← Prob.total μ]
rw [tsum_bool]
rw [add_comm]
```
:::
:::solution
```
rw [add_comm, ← tsum_bool, Prob.total]
```
:::
:::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] (h : μ true = 0) : μ false = ⟦1 ‖ 0, 1⟧") (new := "zero_add") (uses := "mass_total, zero_add, coin_total, add_zero, mul_zero, rw")
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

:::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] (b : Bool) : μ b ≤ 1") (lemma := "mass_le_one") (new := "le_self_add, exact") (uses := "mass_total, add_comm, le_self_add, coin_total, add_assoc, <;>, cases, exact, rw")
::::hint (anchor := "item:exact")
:::en
`exact h`: closes a goal that is exactly `h`.
:::

:::de
`exact h`: schließt ein Ziel, das genau `h` ist.
:::
::::
:::en
*At most one.* Each mass is a part of the whole mass, so at most one.
:::

:::de
*Höchstens eins.* Jede Masse ist ein Teil der ganzen Masse, also höchstens eins.
:::

:::proofen
The `1` is the whole mass, `mass_total μ`, and each mass is one of its summands:
`le_self_add : a ≤ a + c`. Where the summands stand the wrong way round, `add_comm : a + b = b + a`
turns the sum round. `mass_total μ` is your theorem for this `μ`: a rule with a blank, and what goes
into the blank is written behind it. The new tactic `exact h` closes a goal that is exactly `h`.
:::

:::proofde
Die `1` ist die ganze Masse, `mass_total μ`, und jede Masse ist einer ihrer Summanden:
`le_self_add : a ≤ a + c`. Wo die Summanden falsch herum stehen, dreht `add_comm : a + b = b + a`
die Summe um. `mass_total μ` ist dein Satz für dieses `μ`: eine Regel mit einer Leerstelle, und was
in die Leerstelle kommt, schreibt man dahinter. Die neue Taktik `exact h` schließt ein Ziel, das
genau `h` ist.
:::
:::solution
```
rw [← mass_total μ]
cases b
rw [add_comm]
exact le_self_add
exact le_self_add
```
:::
:::solution
```
cases b
rw [← mass_total μ, add_comm]
exact le_self_add
rw [← mass_total μ]
exact le_self_add
```
:::
:::solution
```
cases b <;> rw [← mass_total μ]
rw [add_comm]
exact le_self_add
exact le_self_add
```
:::
:::::

:::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] (b : Bool) : μ b ≠ ⟦⊤ ‖ 0, 1, ⊤⟧") (lemma := "mass_ne_top") (new := "apply, ne_top_of_le_ne_top, ENNReal.one_ne_top") (uses := "ne_top_of_le_ne_top, ENNReal.one_ne_top, mass_le_one, apply, exact")
:::en
*Finite.* Masses are numbers in $`[0, \infty]`; a mass of a distribution is finite, `≠ ⊤`
(`⊤` is $`\infty`): it is at most one, and one is finite.
:::

:::de
*Endlich.* Massen sind Zahlen in $`[0, \infty]`; eine Masse einer Verteilung ist endlich, `≠ ⊤`
(`⊤` ist $`\infty`): Sie ist höchstens eins, und eins ist endlich.
:::

:::proofen
`ne_top_of_le_ne_top : b ≠ ⊤ → a ≤ b → a ≠ ⊤`. The new tactic `apply h` works backwards: the goal is
the conclusion of `h`, and what `h` still needs becomes the new goal. What `h` needs can also be
given along, `apply h h₁`: here `ENNReal.one_ne_top : 1 ≠ ⊤`.
:::

:::proofde
`ne_top_of_le_ne_top : b ≠ ⊤ → a ≤ b → a ≠ ⊤`. Die neue Taktik `apply h` arbeitet rückwärts: Das
Ziel ist die Folgerung von `h`, und was `h` noch braucht, wird das neue Ziel. Was `h` braucht, kann
man auch gleich mitgeben, `apply h h₁`: hier `ENNReal.one_ne_top : 1 ≠ ⊤`.
:::
:::solution
```
apply ne_top_of_le_ne_top ENNReal.one_ne_top
exact mass_le_one μ b
```
:::
:::solution
```
exact ne_top_of_le_ne_top ENNReal.one_ne_top (mass_le_one μ b)
```
:::
:::solution
```
apply ne_top_of_le_ne_top ENNReal.one_ne_top
apply mass_le_one
```
:::
:::::

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

::::leanonly (proof := "(f : Bool → Bool) (μ : DiscreteMeasure Bool) (b : Bool) : (μ.map f) b = (bif f true == b then μ true else 0) + (bif f false == b then μ false else 0)") (new := "map_apply, sum_with") (lemma := "map_bool") (board := "maps") (uses := "map_apply, sum_with, Fintype.sum_bool, rw")
:::en
*Where the mass goes.* A gate after a distribution `μ` is a move, `μ.map f`: it takes each point `a`
with its mass `μ a` to `f a`. On the board, `μ` goes through each of the four maps
`Bool → Bool`. Fill in the mass at `true` after each; the one at `false` is the rest.
:::

:::de
*Wohin die Masse geht.* Ein Baustein nach einer Verteilung `μ` ist ein Zug, `μ.map f`: Er bringt
jeden Punkt `a` mit seiner Masse `μ a` nach `f a`. Auf dem Spielfeld geht `μ` durch jede der
vier Abbildungen `Bool → Bool`. Trag nach jeder die Masse bei `true` ein; die bei `false` ist der
Rest.
:::

:::proofen
The mass at `b` is the sum of the masses of the points with `f a = b`:
`map_apply : (μ.map f) b = ∑ a with f a = b, μ a`. `sum_with` writes this sum as a sum over all
points, with a test. Your result becomes the lemma `map_bool`.
:::

:::proofde
Die Masse bei `b` ist die Summe der Massen der Punkte mit `f a = b`:
`map_apply : (μ.map f) b = ∑ a with f a = b, μ a`. `sum_with` schreibt diese Summe als Summe über
alle Punkte, mit einem Test. Dein Ergebnis wird das Lemma `map_bool`.
:::
:::solution
```
rw [map_apply, sum_with, Fintype.sum_bool]
```
:::
:::solution
```
rw [map_apply]
rw [sum_with]
rw [Fintype.sum_bool]
```
:::
::::

::::leanonly (proof := "(f : Bool → Bool) (μ : DiscreteMeasure Bool) : (μ.map f) true = (bif f true then μ true else 0) + (bif f false then μ false else 0)") (lemma := "map_true") (uses := "map_bool, beq_true, map_apply, sum_with, Fintype.sum_bool, <;>, cases, rfl, rw")
:::en
*The rule of the gates.* `map_bool` at `b = true`.
:::

:::de
*Die Regel der Bausteine.* `map_bool` bei `b = true`.
:::

:::proofen
What is left after `map_bool` are tests against `true`.
:::

:::proofde
Nach `map_bool` bleiben Tests gegen `true`.
:::
:::solution
```
rw [map_bool]
rw [beq_true, beq_true]
```
:::
:::solution
```
rw [map_apply, sum_with, Fintype.sum_bool, beq_true, beq_true]
```
:::
:::solution
```
rw [map_bool]
cases f true <;> cases f false <;> rfl
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

::::leanonly (proof := "(μ : DiscreteMeasure Bool) : (μ.map not) true = ⟦μ false ‖ μ true, μ false⟧") (lemma := "map_not_true") (uses := "map_true, Bool.not_true, Bool.not_false, Bool.cond_false, Bool.cond_true, zero_add, map_bool, beq_true, add_zero, mul_zero, rw")
:::en
*Boss: where does the mass go?* `not` swaps the two points. The mass at `true` after the move: where
did it come from?
:::

:::de
*Endgegner: Wohin geht die Masse?* `not` vertauscht die beiden Punkte. Die Masse bei `true` nach dem
Zug: Woher kam sie?
:::

:::proofen
Your rule `map_true`, for the move `not`. What you prove is unlocked as `map_not_true`.
:::

:::proofde
Deine Regel `map_true`, für den Zug `not`. Was du beweist, wird als `map_not_true` freigeschaltet.
:::
:::solution
```
rw [map_true]
rw [Bool.not_true, Bool.not_false]
rw [Bool.cond_false, Bool.cond_true, zero_add]
```
:::
:::solution
```
rw [map_true, Bool.not_true, Bool.not_false, Bool.cond_false, Bool.cond_true, zero_add]
```
:::
:::solution
```
rw [map_bool, beq_true, beq_true, Bool.not_true, Bool.not_false, Bool.cond_false, Bool.cond_true, zero_add]
```
:::
::::
