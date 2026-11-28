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
up to one. A move `μ.map f` with a map `f : Bool → Bool` takes each mass to its image. This world proves what holds for every such `μ`, and has one example: the sure
distribution `pure b`. The coins come in the next world.
:::

:::de
Eine Verteilung auf `Bool` ist in Lean `μ : DiscreteMeasure Bool`: Sie gibt jedem der beiden Punkte
seine *Masse*, `μ true` und `μ false`, die Höhen ihrer beiden Säulen. `[Prob μ]` sagt, dass die beiden
Massen zusammen eins ergeben. Ein Zug `μ.map f` mit einer Abbildung `f : Bool → Bool` bringt jede Masse
zu ihrem Bild. Diese Welt beweist, was für jedes solche `μ` gilt, und hat ein Beispiel:
die sichere Verteilung `pure b`. Die Münzen kommen in der nächsten Welt.
:::

:::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] : μ true + μ false = 1") (lemma := "mass_total") (new := "Prob.total") (uses := "Prob.total, tsum_bool, add_comm, add_assoc, rw")
:::en
*The whole mass.* `[Prob μ]` says: `μ` is a distribution, its masses add up to one. On `Bool` there
are two of them.
:::

:::de
*Die ganze Masse.* `[Prob μ]` sagt: `μ` ist eine Verteilung, ihre Massen ergeben zusammen eins. Auf
`Bool` sind es zwei.
:::

::::hint (anchor := "word:DiscreteMeasure")
:::en
`μ : DiscreteMeasure Bool` is a distribution on `Bool`: a mass in $`[0, \infty]` at each point,
`μ true` and `μ false`.
:::

:::de
`μ : DiscreteMeasure Bool` ist eine Verteilung auf `Bool`: eine Masse in $`[0, \infty]` an jedem
Punkt, `μ true` und `μ false`.
:::
::::

::::hint (anchor := "word:[Prob μ]")
:::en
`[Prob μ]` is an assumption about `μ`: its masses add up to one, `Prob.total μ : ∑' a, μ a = 1`.
:::

:::de
`[Prob μ]` ist eine Annahme über `μ`: Seine Massen ergeben zusammen eins, `Prob.total μ : ∑' a, μ a = 1`.
:::
::::

:::proofen
A distribution is, in Lean, its masses (its *weight* function):

```
structure DiscreteMeasure (α : Type) where
  weight : α → ℝ≥0∞
```

`ℝ≥0∞` (in Lean `ENNReal`) are the numbers from 0 to ∞, ∞ included: a mass is never negative.
(`μ x` is `μ.weight x`.)

`Prob.total μ : ∑' a, μ a = 1` is a sum over all points, `∑'`; read from right to left, it makes the
`1` of the goal this sum. `tsum_bool` (from *Bool*) writes a sum over `Bool` as its two terms, `false` first;
`add_comm : a + b = b + a` turns them round.
:::

:::proofde
Eine Verteilung ist in Lean ihre Massen (ihre *Gewichtsfunktion*):

```
structure DiscreteMeasure (α : Type) where
  weight : α → ℝ≥0∞
```

`ℝ≥0∞` (in Lean `ENNReal`) sind die Zahlen von 0 bis ∞, ∞ eingeschlossen: Eine Masse ist nie negativ.
(`μ x` ist `μ.weight x`.)

`Prob.total μ : ∑' a, μ a = 1` ist eine Summe über alle Punkte, `∑'`; von rechts nach links gelesen
macht sie die `1` des Ziels zu dieser Summe. `tsum_bool` (aus *Bool*) schreibt eine Summe über
`Bool` als ihre zwei Summanden, `false` zuerst; `add_comm : a + b = b + a` dreht sie um.
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

:::::quiz (tactic := "exact mass_total _") (statements := "(μ : DiscreteMeasure Bool) [Prob μ] : μ true + μ false = 1 ;; (μ : DiscreteMeasure Bool) [Prob μ] : μ false + μ true = 1 ;; (μ : DiscreteMeasure Bool) [Prob μ] : 1 = μ true + μ false ;; (b : Bool) : (pure b : DiscreteMeasure Bool) true + (pure b : DiscreteMeasure Bool) false = 1 ;; (μ : DiscreteMeasure Bool) [Prob μ] : (μ.map not) true + (μ.map not) false = 1") (answer := "1, 4, 5") (context := "Lean/Rules.lean")
:::en
*Exactly.* `exact mass_total _` closes a goal that is exactly `mass_total` for some distribution; the
blank `_` Lean fills in itself. Which of these does it prove?
:::

:::de
*Genau.* `exact mass_total _` schließt ein Ziel, das genau `mass_total` für eine Verteilung ist; die
Leerstelle `_` füllt Lean selbst. Welche davon beweist es?
:::

::::hint (anchor := "solved")
:::en
`exact` does not turn round: `μ false + μ true` and `1 = …` are not the form of `mass_total`, and
Lean finds no distribution for the blank. The sure `pure b` and a move `μ.map not` are distributions
too, `[Prob …]` holds for them.
:::

:::de
`exact` dreht nichts um: `μ false + μ true` und `1 = …` haben nicht die Form von `mass_total`, und
Lean findet keine Verteilung für die Leerstelle. Das sichere `pure b` und ein Zug `μ.map not` sind auch
Verteilungen, `[Prob …]` gilt für sie.
:::
::::
:::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] (h : μ true = 0) : μ false = ⟦1 ‖ 0, 1⟧") (uses := "mass_total, zero_add, coin_total, add_zero, mul_zero, rw")
:::hint (anchor := "none")
:::

:::en
*Nothing at true.* A distribution has the total mass one. If nothing lies at `true`, everything lies at `false`.
:::

:::de
*Nichts bei true.* Eine Verteilung hat die Gesamtmasse eins. Liegt bei `true` nichts, liegt alles bei `false`.
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

:::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] (b : Bool) : μ b ≤ 1") (lemma := "mass_le_one") (uses := "mass_total, add_comm, le_self_add, coin_total, add_assoc, <;>, cases, exact, rw")
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
into the blank is written behind it.
:::

:::proofde
Die `1` ist die ganze Masse, `mass_total μ`, und jede Masse ist einer ihrer Summanden:
`le_self_add : a ≤ a + c`. Wo die Summanden falsch herum stehen, dreht `add_comm : a + b = b + a`
die Summe um. `mass_total μ` ist dein Satz für dieses `μ`: eine Regel mit einer Leerstelle, und was
in die Leerstelle kommt, schreibt man dahinter.
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

:::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] (b : Bool) : μ b ≠ ⟦∞ ‖ 0, 1, ∞⟧") (lemma := "mass_ne_top") (uses := "ne_top_of_le_ne_top, ENNReal.one_ne_top, mass_le_one, apply, exact")
:::en
*Finite.* Masses are numbers in $`[0, \infty]`; a mass of a distribution is finite, `≠ ∞`:
it is at most one, and one is finite.
:::

:::de
*Endlich.* Massen sind Zahlen in $`[0, \infty]`; eine Masse einer Verteilung ist endlich, `≠ ∞`:
Sie ist höchstens eins, und eins ist endlich.
:::

:::proofen
As in *ENNReal*: `apply ne_top_of_le_ne_top ENNReal.one_ne_top`, and what is left is `μ b ≤ 1`.
:::

:::proofde
Wie in *ENNReal*: `apply ne_top_of_le_ne_top ENNReal.one_ne_top`, und übrig bleibt `μ b ≤ 1`.
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

::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] (b : Bool) : μ b = ⟦1 - μ (!b) ‖ 1 - μ (!b), μ (!b) - 1, 1 - μ b⟧") (lemma := "mass_not") (uses := "Bool.not_false, mass_total, ENNReal.add_sub_cancel_left, mass_ne_top, Bool.not_true, add_comm, coin_total, add_assoc, cases, exact, rw")
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
finite: `ENNReal.add_sub_cancel_left (h : a ≠ ∞) : a + b - a = b`, and `mass_ne_top : μ b ≠ ∞` says
that a mass is finite. The hypothesis is written behind the rule; without it, `rw` leaves it as a
second goal.
:::

:::proofde
`mass_total μ : μ true + μ false = 1`: Die Masse auf der einen Seite ist das, was der anderen zu
eins fehlt. Der Punkt `b` ist `false` oder `true`.

Massen sind Zahlen in $`[0, \infty]` (`ℝ≥0∞`); wegnehmen darf man, wenn das Weggenommene endlich
ist: `ENNReal.add_sub_cancel_left (h : a ≠ ∞) : a + b - a = b`, und `mass_ne_top : μ b ≠ ∞` sagt,
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
By the definition of `pure`,

```
def pure (a : α) : DiscreteMeasure α := ⟨({a} : Set α).indicator 1⟩
```

the mass is `1` on the set `{a}` and `0` outside it. The game writes this as the new rule
`pure_apply : (pure a) b = bif a == b then 1 else 0`.  What you prove is unlocked as `pure_true`.
:::

:::proofde
Nach der Definition von `pure`,

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
*The mass at true after a move.* `map_bool` at `b = true`.
:::

:::de
*Die Masse bei true nach einem Zug.* `map_bool` bei `b = true`.
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

::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] : μ.map (fun x => x) = ⟦μ ‖ μ, μ.map not⟧") (lemma := "map_id") (uses := "bool_ext, map_true, Bool.cond_true, Bool.cond_false, add_zero, map_bool, Bool.true_beq, Bool.false_beq, Bool.not_false, zero_add, Bool.not_true, add_comm, mul_zero, add_assoc, apply, cases, ext, rw")
:::en
*Doing nothing.* The move `fun x => x` leaves every point where it is.
:::

:::de
*Nichts tun.* Der Zug `fun x => x` lässt jeden Punkt, wo er ist.
:::

:::proofen
One bar is enough (`bool_ext`): compare the masses at `true`, with `map_true`. You prove it on `Bool`; it holds for every type, and it is unlocked as `map_id` in
this general form.
:::

:::proofde
Eine Säule genügt (`bool_ext`): Vergleiche die Massen bei `true`, mit `map_true`. Du beweist es auf `Bool`; es gilt für jeden Typ und wird in dieser
allgemeinen Form als `map_id` freigeschaltet.
:::
:::solution
```
apply bool_ext
rw [map_true, Bool.cond_true, Bool.cond_false, add_zero]
```
:::
:::solution
```
apply bool_ext
rw [map_true]
rw [Bool.cond_true, Bool.cond_false]
rw [add_zero]
```
:::
:::solution
```
ext b
rw [map_bool, Bool.true_beq, Bool.false_beq]
cases b
rw [Bool.not_false, Bool.cond_false, Bool.cond_true, zero_add]
rw [Bool.not_true, Bool.cond_true, Bool.cond_false, add_comm, zero_add]
```
:::
::::

:::::quiz (tactic := "rw [Bool.not_not]") (context := "Lean/Rules.lean") (statements := "(b : Bool) : (!(!b)) = b ;; (μ : DiscreteMeasure Bool) : μ.map (fun b => !(!b)) = μ.map (fun b => b) ;; (f : Bool → Bool) (b : Bool) : f (!(!b)) = f b ;; : (fun b : Bool => !(!b)) = (fun b => b) ;; (a : Bool) : (a && !(!a)) = (a && a)") (answer := "1, 3, 5")
::::hint (anchor := "solved")
:::en
Why two fail: in `fun b => !(!b)` the `b` is *bound*, a name that exists only inside the `fun`.
`rw` rewrites a part of the goal that stands there on its own, and `!(!b)` with a bound `b` is no such
part: Lean does not find the pattern. In the other three, `b` and `a` are variables of the statement.
The next level brings a tactic that rewrites under `fun`.
:::

:::de
Warum zwei scheitern: In `fun b => !(!b)` ist das `b` *gebunden*, ein Name, den es nur innerhalb des
`fun` gibt. `rw` schreibt einen Teil des Ziels um, der für sich dasteht, und `!(!b)` mit gebundenem
`b` ist kein solcher Teil: Lean findet das Muster nicht. In den anderen drei sind `b` und `a`
Variablen der Aussage. Das nächste Level bringt eine Taktik, die unter `fun` umschreibt.
:::
::::
:::en
*Where does `rw` fail?* Your lemma from *Bool*, `Bool.not_not : (!(!b)) = b`. Every statement here has a `!(!…)` in it, and yet `rw [Bool.not_not]` proves only some of them. Which? Look at where the `b` comes from.
:::

:::de
*Wo scheitert `rw`?* Dein Lemma aus *Bool*, `Bool.not_not : (!(!b)) = b`. Jede Aussage hier enthält ein `!(!…)`, und doch beweist `rw [Bool.not_not]` nur manche. Welche? Schau, woher das `b` kommt.
:::
:::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) : μ.map (fun x => !(!x)) = ⟦μ ‖ μ, μ.map not⟧") (new := "simp_rw") (uses := "Bool.not_not, map_id, exact, rw, simp_rw")
:::en
*Turned over twice, in one move.* The move `fun x => !(!x)`: turn over, and turn over again.
:::

:::de
*Zweimal umgedreht, in einem Zug.* Der Zug `fun x => !(!x)`: umdrehen, und nochmal umdrehen.
:::

:::proofen
`rw [Bool.not_not]` does not find `!(!x)`, as in the quiz before: the `x` in `fun x => …` is a
*bound* name, like the index `x` of a sum `∑ x, …`, and `rw` rewrites only parts without bound
names. The new tactic `simp_rw [rules]` is `rw`, also under bound names.
:::

:::proofde
`rw [Bool.not_not]` findet `!(!x)` nicht, wie im Quiz davor: Das `x` in `fun x => …` ist ein
*gebundener* Name, wie der Index `x` einer Summe `∑ x, …`, und `rw` schreibt nur Teile ohne
gebundene Namen um. Die neue Taktik `simp_rw [Regeln]` ist `rw`, auch unter gebundenen Namen.
:::
:::solution
```
simp_rw [Bool.not_not]
rw [map_id]
```
:::
:::solution
```
simp_rw [Bool.not_not, map_id]
```
:::
:::solution
```
simp_rw [Bool.not_not]
exact map_id μ
```
:::
::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) : (μ.map not) true = ⟦μ false ‖ μ true, μ false⟧") (lemma := "map_not_true") (uses := "map_true, Bool.not_true, Bool.not_false, Bool.cond_false, Bool.cond_true, zero_add, map_bool, beq_true, add_zero, mul_zero, rw")
:::en
*Where does the mass go?* `not` swaps the two points. The mass at `true` after the move: where
did it come from?
:::

:::de
*Wohin geht die Masse?* `not` vertauscht die beiden Punkte. Die Masse bei `true` nach dem
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

::::leanonly (proof := "(f : Bool → Bool) (x y : ℝ≥0∞) : (bif f true then x else 0) + (bif f true then y else 0) = bif f true then ⟦x + y ‖ x + y, x, y, x * y⟧ else 0") (lemma := "cond_add_cond") (uses := "Bool.cond_false, zero_add, Bool.cond_true, add_zero, mul_zero, cases, rw, simp_rw")
:::en
*Two masses behind one test.* Twice the same test `f true`: once with the mass `x`, once with the
mass `y`.
:::

:::de
*Zwei Massen hinter einem Test.* Zweimal derselbe Test `f true`: einmal mit der Masse `x`, einmal
mit der Masse `y`.
:::

:::proofen
With `cases f true` (from *Bool*); with `simp_rw` every `bif false then … else …` goes at once. You prove it
for the test `f true`; it holds for every test `c : Bool`, and it is unlocked as
`cond_add_cond : (bif c then x else 0) + (bif c then y else 0) = bif c then x + y else 0`.
:::

:::proofde
Mit `cases f true` (aus *Bool*); mit `simp_rw` geht jedes `bif false then … else …` auf einmal. Du beweist es für
den Test `f true`; es gilt für jeden Test `c : Bool` und wird freigeschaltet als
`cond_add_cond : (bif c then x else 0) + (bif c then y else 0) = bif c then x + y else 0`.
:::
:::solution
```
cases f true
simp_rw [Bool.cond_false]
rw [zero_add]
simp_rw [Bool.cond_true]
```
:::
:::solution
```
cases f true
rw [Bool.cond_false, Bool.cond_false, Bool.cond_false, zero_add]
rw [Bool.cond_true, Bool.cond_true, Bool.cond_true]
```
:::
:::solution
```
cases f true
simp_rw [Bool.cond_false, zero_add]
simp_rw [Bool.cond_true]
```
:::
::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) (f g : Bool → Bool) : (μ.map f).map g = μ.map ⟦fun x => g (f x) ‖ fun x => g (f x), fun x => f (g x), g⟧") (lemma := "map_map") (uses := "map_bool, Bool.false_beq, Bool.not_true, beq_self_eq_true, Bool.cond_false, Bool.cond_true, zero_add, Bool.cond_self, cond_add_cond, Bool.true_beq, Bool.not_false, add_comm, beq_true, add_zero, mul_zero, add_assoc, cases, ext, rw, simp_rw")
:::en
*Boss: two moves are one.* First the move `f`, then the move `g`: which one move is that?
:::

:::de
*Endgegner: Zwei Züge sind einer.* Erst der Zug `f`, dann der Zug `g`: Welcher eine Zug ist das?
:::

:::proofen
Compare the masses at every point (`ext b`), with `map_bool`. Then the cases `f true` and `f false`
(`cases f true`, from *Bool*); where two masses stand behind the same test, `cond_add_cond` (the
level before) makes them one. You prove it on `Bool`; it holds for every type, and it is unlocked as
`map_map` in this general form.
:::

:::proofde
Vergleiche die Massen an jedem Punkt (`ext b`), mit `map_bool`. Dann die Fälle `f true` und `f false`
(`cases f true`, aus *Bool*); wo zwei Massen hinter demselben Test stehen, macht `cond_add_cond` (das
Level davor) eine daraus. Du beweist es auf `Bool`; es gilt für jeden Typ und wird in dieser allgemeinen
Form als `map_map` freigeschaltet.
:::
:::solution
```
ext b
simp_rw [map_bool]
cases f true
cases f false
rw [Bool.false_beq, Bool.not_true, beq_self_eq_true]
simp_rw [Bool.cond_false, Bool.cond_true]
rw [zero_add, Bool.cond_self, zero_add, cond_add_cond]
simp_rw [Bool.false_beq, Bool.true_beq, Bool.not_true, Bool.not_false]
simp_rw [Bool.cond_false, Bool.cond_true]
rw [zero_add, add_comm (μ true), zero_add, add_comm]
cases f false
simp_rw [Bool.false_beq, Bool.true_beq, Bool.not_true, Bool.not_false]
simp_rw [Bool.cond_false, Bool.cond_true]
rw [add_comm (μ true), zero_add, zero_add]
simp_rw [Bool.true_beq]
simp_rw [Bool.cond_false, Bool.cond_true]
rw [zero_add, Bool.cond_self, add_comm, zero_add, cond_add_cond]
```
:::
:::solution
```
ext b
rw [map_bool, map_bool, map_bool, map_bool]
cases f true
cases f false
rw [beq_true, beq_self_eq_true]
simp_rw [Bool.cond_false, Bool.cond_true]
rw [zero_add, Bool.cond_self, zero_add, cond_add_cond]
rw [beq_true, beq_true, beq_self_eq_true, Bool.true_beq]
simp_rw [Bool.cond_false, Bool.cond_true]
rw [zero_add, add_comm (μ true), zero_add, add_comm]
cases f false
rw [beq_true, beq_true, Bool.true_beq, beq_self_eq_true]
simp_rw [Bool.cond_false, Bool.cond_true]
rw [add_comm (μ true), zero_add, zero_add]
rw [beq_true, Bool.true_beq]
simp_rw [Bool.cond_false, Bool.cond_true]
rw [zero_add, Bool.cond_self, add_comm, zero_add, cond_add_cond]
```
:::
:::solution
```
ext b
simp_rw [map_bool]
cases f true
cases f false
rw [Bool.false_beq, Bool.not_true, beq_self_eq_true]
simp_rw [Bool.cond_false, Bool.cond_true]
rw [zero_add, Bool.cond_self, zero_add, cond_add_cond]
simp_rw [Bool.false_beq, Bool.true_beq, Bool.not_true, Bool.not_false]
simp_rw [Bool.cond_false, Bool.cond_true]
rw [zero_add, add_zero, add_comm]
cases f false
simp_rw [Bool.false_beq, Bool.true_beq, Bool.not_true, Bool.not_false]
simp_rw [Bool.cond_false, Bool.cond_true]
rw [add_zero, zero_add]
simp_rw [Bool.true_beq]
simp_rw [Bool.cond_false, Bool.cond_true]
rw [zero_add, Bool.cond_self, add_zero, cond_add_cond]
```
:::
::::
