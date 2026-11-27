import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Maps" =>

%%%
htmlSplit := .never
%%%

:::en
Maps on `Bool`, and moves with them. There are exactly four maps `Bool → Bool`: `id`, `not`, always
`true` (`fun _ => true`) and always `false` (`fun _ => false`). A statement about an unknown map
`f : Bool → Bool` holds for every map when it holds for each of the four.
:::

:::de
Abbildungen auf `Bool`, und Züge mit ihnen. Es gibt genau vier Abbildungen `Bool → Bool`: `id`,
`not`, immer `true` (`fun _ => true`) und immer `false` (`fun _ => false`). Eine Aussage über eine
unbekannte Abbildung `f : Bool → Bool` gilt für jede Abbildung, wenn sie für jede der vier gilt.
:::

::::leanonly (proof := "(f : Bool → Bool) (b : Bool) : f (f (f b)) = ⟦f b ‖ b, f b, f (f b)⟧") (lemma := "Bool.apply_apply_apply") (new := "revert, decide") (group := "bool") (uses := "decide, revert")
:::en
*Three times.* Whatever map `f : Bool → Bool` is: what does it do, applied three times? Check it for
`not` and for always `true`. In Lean the new tactics `revert` and `decide` check it, in every case at once.
:::

:::de
*Dreimal.* Welche Abbildung `f : Bool → Bool` auch immer: Was tut sie, dreimal angewandt? Prüf es
für `not` und für immer `true`. In Lean prüfen es die neuen Taktiken `revert` und `decide`, in allen Fällen auf einmal.
:::

:::proofen
No rule says what `f` does, so there is nothing to rewrite. But there are only four maps
`Bool → Bool`, and with the two values of `b` these are eight cases. Two new tactics: `revert f b`
takes the variables back into the statement, here `∀ f b, f (f (f b)) = f b`; `decide` reduces a
statement about finitely many cases until it is `true` or `false`, and so checks every case. (For
one unknown `f` there is nothing to compute: `decide` alone does not work.) Your result is unlocked
as `Bool.apply_apply_apply`.
:::

:::proofde
Keine Regel sagt, was `f` tut; es gibt also nichts umzuschreiben. Aber es gibt nur vier Abbildungen
`Bool → Bool`, und mit den zwei Werten von `b` sind das acht Fälle. Zwei neue Taktiken: `revert f b`
nimmt die Variablen zurück in die Aussage, hier `∀ f b, f (f (f b)) = f b`; `decide` reduziert eine
Aussage über endlich viele Fälle, bis sie `true` oder `false` ist, und prüft so jeden Fall. (Für ein
unbekanntes `f` gibt es nichts auszurechnen: `decide` allein geht nicht.) Dein Ergebnis wird als
`Bool.apply_apply_apply` freigeschaltet.
:::
:::solution
```
revert f b
decide
```
:::
::::

::::quiz (tactic := "revert f b; decide") (statements := "(f : Bool → Bool) (b : Bool) : f (f b) = b ;; (f : Bool → Bool) (b : Bool) : f (f (f (f b))) = f (f b) ;; (f : Bool → Bool) (b : Bool) : f (f b) = f b ;; (f : Bool → Bool) (b : Bool) : (f b && !f b) = false ;; (f : Bool → Bool) (b : Bool) : (f b || f (!b)) = true") (answer := "2, 4")
:::en
*For every map?* Which of these statements hold for every map `f : Bool → Bool` and every `b`? Go through the four maps. Lean checks your choice with `revert f b` and `decide`.
:::

:::de
*Für jede Abbildung?* Welche dieser Aussagen gelten für jede Abbildung `f : Bool → Bool` und jedes `b`? Geh die vier Abbildungen durch. Lean prüft deine Wahl mit `revert f b` und `decide`.
:::
::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) : μ.map (fun x => x) = ⟦μ ‖ μ, μ.map not⟧") (lemma := "map_id") (new := "Bool.false_beq") (uses := "map_apply, Bool.true_beq, Bool.false_beq, Bool.not_false, Bool.cond_false, Bool.cond_true, zero_add, Bool.not_true, add_comm, add_zero, mul_zero, add_assoc, cases, ext, rw")
:::en
*Doing nothing.* The move `fun x => x` leaves every point where it is.
:::

:::de
*Nichts tun.* Der Zug `fun x => x` lässt jeden Punkt, wo er ist.
:::

:::proofen
Compare the masses at every point (`ext`, from *One Coin*), with the definition `map_apply`. The
tests `true == b` and `false == b` are `b` and `!b`: `Bool.true_beq` from *Masses*, and the new rule
`Bool.false_beq`. You prove it on `Bool`; it holds for every type, and it is unlocked as `map_id` in
this general form.
:::

:::proofde
Vergleiche die Massen an jedem Punkt (`ext`, aus *Eine Münze*), mit der Definition `map_apply`. Die
Tests `true == b` und `false == b` sind `b` und `!b`: `Bool.true_beq` aus *Massen*, und die neue
Regel `Bool.false_beq`. Du beweist es auf `Bool`; es gilt für jeden Typ und wird in dieser
allgemeinen Form als `map_id` freigeschaltet.
:::
:::solution
```
ext b
rw [map_apply, Bool.true_beq, Bool.false_beq]
cases b
rw [Bool.not_false, Bool.cond_false, Bool.cond_true, zero_add]
rw [Bool.not_true, Bool.cond_true, Bool.cond_false, add_comm, zero_add]
```
:::
::::

::::quiz (tactic := "rw [Bool.not_not]") (context := "Lean/Rules.lean") (statements := "(b : Bool) : (!(!b)) = b ;; (μ : DiscreteMeasure Bool) : μ.map (fun b => !(!b)) = μ.map (fun b => b) ;; (f : Bool → Bool) (b : Bool) : f (!(!b)) = f b ;; : (fun b : Bool => !(!b)) = (fun b => b) ;; (a : Bool) : (a && !(!a)) = (a && a)") (answer := "1, 3, 5")
:::en
*Where does `rw` fail?* Your lemma from *Bool*, `Bool.not_not : (!(!b)) = b`. Every statement here has a `!(!…)` in it, and yet `rw [Bool.not_not]` proves only some of them. Which? Look at where the `b` comes from.
:::

:::de
*Wo scheitert `rw`?* Dein Lemma aus *Bool*, `Bool.not_not : (!(!b)) = b`. Jede Aussage hier enthält ein `!(!…)`, und doch beweist `rw [Bool.not_not]` nur manche. Welche? Schau, woher das `b` kommt.
:::
::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) : μ.map (fun x => !(!x)) = ⟦μ ‖ μ, μ.map not⟧") (new := "simp_rw") (uses := "Bool.not_not, map_id, rw, simp_rw")
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
::::

::::leanonly (proof := "(f : Bool → Bool) (x : ℝ≥0∞) : (bif f true then x else 0) + (bif f true then 0 else x) = ⟦x ‖ x + x, x, 0⟧") (uses := "Bool.cond_false, zero_add, Bool.cond_true, add_comm, add_zero, mul_zero, add_assoc, cases, rw")
:::en
*A test is `true` or `false`.* The mass `x` behind the test `f true`, once in the `then` branch and once in the `else` branch. What `f` does is unknown.
:::

:::de
*Ein Test ist `true` oder `false`.* Die Masse `x` hinter dem Test `f true`, einmal im `then`-Zweig und einmal im `else`-Zweig. Was `f` tut, ist unbekannt.
:::

:::proofen
`f true` is not a variable, but it is a `Bool`, so it is `true` or `false`: `cases f true` goes
through both values, as `cases x` does for a variable.
:::

:::proofde
`f true` ist keine Variable, aber ein `Bool`, also `true` oder `false`: `cases f true` geht beide
Werte durch, wie `cases x` für eine Variable.
:::
:::solution
```
cases f true
rw [Bool.cond_false, Bool.cond_false, zero_add]
rw [Bool.cond_true, Bool.cond_true, add_comm, zero_add]
```
:::
::::

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
As in the level before; with `simp_rw` every `bif false then … else …` goes at once. You prove it
for the test `f true`; it holds for every test `c : Bool`, and it is unlocked as
`cond_add_cond : (bif c then x else 0) + (bif c then y else 0) = bif c then x + y else 0`.
:::

:::proofde
Wie im Level davor; mit `simp_rw` geht jedes `bif false then … else …` auf einmal. Du beweist es für
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
::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) (f g : Bool → Bool) : (μ.map f).map g = μ.map ⟦fun x => g (f x) ‖ fun x => g (f x), fun x => f (g x), g⟧") (lemma := "map_map") (uses := "map_apply, Bool.false_beq, Bool.not_true, beq_self_eq_true, Bool.cond_false, Bool.cond_true, zero_add, Bool.cond_self, cond_add_cond, Bool.true_beq, Bool.not_false, add_comm, add_zero, mul_zero, add_assoc, cases, ext, rw, simp_rw")
:::en
*Boss: two moves are one.* First the move `f`, then the move `g`: which one move is that?
:::

:::de
*Boss: Zwei Züge sind einer.* Erst der Zug `f`, dann der Zug `g`: Welcher eine Zug ist das?
:::

:::proofen
You prove it on `Bool`; it holds for every type, and it is unlocked as `map_map` in this general form.
:::

:::proofde
Du beweist es auf `Bool`; es gilt für jeden Typ und wird in dieser allgemeinen Form als `map_map`
freigeschaltet.
:::
:::solution
```
ext b
simp_rw [map_apply]
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
::::
