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

::::leanonly (proof := "(f : Bool → Bool) (b : Bool) : f (f (f b)) = ⟦f b ‖ b, f b, f (f b)⟧") (lemma := "Bool.apply_apply_apply") (new := "revert, decide") (group := "bool") (uses := "-")
:::en
*Three times.* Whatever map `f : Bool → Bool` is: what does it do, applied three times? Check it for
`not` and for always `true`. In Lean the new tactics `revert` and `decide` check it, in every case at once.
:::

:::de
*Dreimal.* Welche Abbildung `f : Bool → Bool` auch immer: Was tut sie, dreimal angewandt? Prüf es
für `not` und für immer `true`. In Lean prüfen es die neuen Taktiken `revert` und `decide`, in allen Fällen auf einmal.
:::

:::proofen
No rule says what `f` does, so there is nothing to rewrite, and no `rw` here. But there are only four maps `Bool → Bool`, `id`, `not` and the two constant ones, and with
the two values of `b` these are eight cases. Two new tactics: `revert f b` takes the variables back
into the statement, here `∀ f b, f (f (f b)) = f b`; then `decide` reduces this statement about
finitely many cases until it is `true` or `false`, and so checks every case. `decide` alone does not
work: for one unknown `f` there is nothing to compute. With
coins this no longer works: a coin `coin p` is a different distribution for every number `p` between
0 and 1, infinitely many cases. There, the rules do the work, and this lemma: it is unlocked as
`Bool.apply_apply_apply`.

*Tip.* `revert f b`, then `decide`.
:::

:::proofde
Keine Regel sagt, was `f` tut; es gibt also nichts umzuschreiben, und hier kein `rw`. Aber es gibt nur vier Abbildungen `Bool → Bool`, `id`, `not` und die
zwei konstanten, und mit den zwei Werten von `b` sind das acht Fälle. Zwei neue Taktiken: `revert f b`
nimmt die Variablen zurück in die Aussage, hier `∀ f b, f (f (f b)) = f b`; dann reduziert `decide`
diese Aussage über endlich viele Fälle, bis sie `true` oder `false` ist, und prüft so jeden Fall.
`decide` allein geht nicht: Für ein unbekanntes `f` gibt es nichts auszurechnen. Mit
Münzen geht das nicht mehr: Eine Münze `coin p` ist für jede Zahl `p`
zwischen 0 und 1 eine andere Verteilung, unendlich viele Fälle. Dort machen die Regeln die Arbeit, und
dieses Lemma: Es wird als `Bool.apply_apply_apply` freigeschaltet.

*Tipp.* `revert f b`, dann `decide`.
:::
:::solution
```
revert f b
decide
```
:::
::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) : μ.map (fun x => x) = ⟦μ ‖ μ, μ.map not⟧") (lemma := "map_id") (new := "Bool.false_beq") (uses := "map_apply, Fintype.sum_bool, Bool.true_beq, Bool.false_beq, Bool.not_false, Bool.cond_false, Bool.cond_true, zero_add, Bool.not_true, add_comm, add_zero, mul_zero, add_assoc")
:::en
*Doing nothing.* The move `fun x => x` leaves every point where it is.
:::

:::de
*Nichts tun.* Der Zug `fun x => x` lässt jeden Punkt, wo er ist.
:::

:::proofen
Compare the masses at every point: `ext b`. `map_apply` and `Fintype.sum_bool` write the mass as two
summands; the tests `true == b` and `false == b` are `b` and `!b` (`Bool.true_beq` from *Masses*,
and the new rule `Bool.false_beq`). Then `cases b`. You prove it on `Bool`; it holds for every type,
and it is unlocked as `map_id` in this general form.

*Tip.* `ext b`, `rw [map_apply, Fintype.sum_bool, Bool.true_beq, Bool.false_beq]`, `cases b`, then
`rw [Bool.not_false, Bool.cond_false, Bool.cond_true, zero_add]` and
`rw [Bool.not_true, Bool.cond_true, Bool.cond_false, add_comm, zero_add]`.
:::

:::proofde
Vergleiche die Massen an jedem Punkt: `ext b`. `map_apply` und `Fintype.sum_bool` schreiben die Masse
als zwei Summanden; die Tests `true == b` und `false == b` sind `b` und `!b` (`Bool.true_beq` aus
*Massen*, und die neue Regel `Bool.false_beq`). Dann `cases b`. Du beweist es auf `Bool`; es gilt für
jeden Typ und wird in dieser allgemeinen Form als `map_id` freigeschaltet.

*Tipp.* `ext b`, `rw [map_apply, Fintype.sum_bool, Bool.true_beq, Bool.false_beq]`, `cases b`, dann
`rw [Bool.not_false, Bool.cond_false, Bool.cond_true, zero_add]` und
`rw [Bool.not_true, Bool.cond_true, Bool.cond_false, add_comm, zero_add]`.
:::
:::solution
```
ext b
rw [map_apply, Fintype.sum_bool, Bool.true_beq, Bool.false_beq]
cases b
rw [Bool.not_false, Bool.cond_false, Bool.cond_true, zero_add]
rw [Bool.not_true, Bool.cond_true, Bool.cond_false, add_comm, zero_add]
```
:::
::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) : μ.map (fun x => !(!x)) = ⟦μ ‖ μ, μ.map not⟧") (new := "simp_rw") (uses := "Bool.not_not, map_id")
:::en
*Turned over twice, in one move.* The move `fun x => !(!x)`: turn over, and turn over again.
:::

:::de
*Zweimal umgedreht, in einem Zug.* Der Zug `fun x => !(!x)`: umdrehen, und nochmal umdrehen.
:::

:::proofen
Your lemma from *Circuits*, `Bool.not_not : (!(!b)) = b`, should make `!(!x)` into `x`. But
`rw [Bool.not_not]` does not find `!(!x)`, though it stands there: the `x` in `fun x => …` is a
*bound* name, like the index `x` of a sum `∑ x, …`, and `rw` rewrites only parts without bound names.
The new tactic `simp_rw [rules]` is `rw`, also under bound names. Then the move does nothing: your
lemma `map_id : μ.map (fun x => x) = μ`.

*Tip.* `simp_rw [Bool.not_not]`, `rw [map_id]`.
:::

:::proofde
Dein Lemma aus *Schaltungen*, `Bool.not_not : (!(!b)) = b`, soll aus `!(!x)` ein `x` machen. Aber
`rw [Bool.not_not]` findet `!(!x)` nicht, obwohl es dasteht: Das `x` in `fun x => …` ist ein
*gebundener* Name, wie der Index `x` einer Summe `∑ x, …`, und `rw` schreibt nur Teile ohne
gebundene Namen um. Die neue Taktik `simp_rw [Regeln]` ist `rw`, auch unter gebundenen Namen. Dann
tut der Zug nichts: dein Lemma `map_id : μ.map (fun x => x) = μ`.

*Tipp.* `simp_rw [Bool.not_not]`, `rw [map_id]`.
:::
:::solution
```
simp_rw [Bool.not_not]
rw [map_id]
```
:::
::::

::::leanonly (proof := "(f : Bool → Bool) (x y : ℝ≥0∞) : (bif f true then x else 0) + (bif f true then y else 0) = bif f true then ⟦x + y ‖ x + y, x, y, x * y⟧ else 0") (lemma := "cond_add_cond") (uses := "Bool.cond_false, zero_add, Bool.cond_true, add_zero, mul_zero")
:::en
*Two masses behind one test.* Twice the same test `f true`: once with the mass `x`, once with the
mass `y`.
:::

:::de
*Zwei Massen hinter einem Test.* Zweimal derselbe Test `f true`: einmal mit der Masse `x`, einmal
mit der Masse `y`.
:::

:::proofen
`f true` is not a variable, but it is a `Bool`, so it is `true` or `false`: `cases f true` goes
through both values, as `cases x` does for a variable. Then the rules from *Circuits*; with
`simp_rw` every `bif false then … else …` goes at once. You prove it for the test `f true`; it holds
for every test `c : Bool`, and it is unlocked as
`cond_add_cond : (bif c then x else 0) + (bif c then y else 0) = bif c then x + y else 0`.

*Tip.* `cases f true`, `simp_rw [Bool.cond_false]`, `rw [zero_add]`, `simp_rw [Bool.cond_true]`.
:::

:::proofde
`f true` ist keine Variable, aber ein `Bool`, also `true` oder `false`: `cases f true` geht beide
Werte durch, wie `cases x` für eine Variable. Dann die Regeln aus *Schaltungen*; mit `simp_rw` geht
jedes `bif false then … else …` auf einmal. Du beweist es für den Test `f true`; es gilt für jeden
Test `c : Bool` und wird freigeschaltet als
`cond_add_cond : (bif c then x else 0) + (bif c then y else 0) = bif c then x + y else 0`.

*Tipp.* `cases f true`, `simp_rw [Bool.cond_false]`, `rw [zero_add]`, `simp_rw [Bool.cond_true]`.
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

::::leanonly (proof := "(μ : DiscreteMeasure Bool) (f g : Bool → Bool) : (μ.map f).map g = μ.map ⟦fun x => g (f x) ‖ fun x => g (f x), fun x => f (g x), g⟧") (lemma := "map_map") (uses := "map_apply, Fintype.sum_bool, Bool.false_beq, Bool.not_true, beq_self_eq_true, Bool.cond_false, Bool.cond_true, zero_add, Bool.cond_self, cond_add_cond, Bool.true_beq, Bool.not_false, add_comm, add_zero, mul_zero, add_assoc")
:::en
*Boss: two moves are one.* First the move `f`, then the move `g`: which one move is that?
:::

:::de
*Boss: Zwei Züge sind einer.* Erst der Zug `f`, dann der Zug `g`: Welcher eine Zug ist das?
:::

:::proofen
Compare the masses at every point `b`, and write each mass as its two summands, also the inner ones
under the sum: `simp_rw`. Then `f` is one of the four maps: `cases f true`, `cases f false`. In each
case the tests with `true` and `false` are your rules from *Masses* and *Circuits*, and your lemma
`cond_add_cond` puts two masses behind one test. You prove it on `Bool`; it holds for every type,
and it is unlocked as `map_map` in this general form.

*Tip.* `ext b`, `simp_rw [map_apply, Fintype.sum_bool]`, `cases f true`, `cases f false`, and then
case by case.
:::

:::proofde
Vergleiche die Massen an jedem Punkt `b`, und schreib jede Masse als ihre zwei Summanden, auch die
inneren unter der Summe: `simp_rw`. Dann ist `f` eine der vier Abbildungen: `cases f true`,
`cases f false`. In jedem Fall sind die Tests mit `true` und `false` deine Regeln aus *Massen* und
*Schaltungen*, und dein Lemma `cond_add_cond` bringt zwei Massen hinter einen Test. Du beweist es
auf `Bool`; es gilt für jeden Typ und wird in dieser allgemeinen Form als `map_map` freigeschaltet.

*Tipp.* `ext b`, `simp_rw [map_apply, Fintype.sum_bool]`, `cases f true`, `cases f false`, und dann
Fall für Fall.
:::
:::solution
```
ext b
simp_rw [map_apply, Fintype.sum_bool]
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
