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

::::leanonly (proof := "(μ : DiscreteMeasure Bool) (f g : Bool → Bool) : (μ.map f).map g = μ.map ⟦fun x => g (f x) ‖ fun x => g (f x), fun x => f (g x), g⟧") (lemma := "map_map") (uses := "map_bool, Bool.false_beq, Bool.not_true, beq_self_eq_true, Bool.cond_false, Bool.cond_true, zero_add, Bool.cond_self, cond_add_cond, Bool.true_beq, Bool.not_false, add_comm, beq_true, add_zero, mul_zero, add_assoc, cases, ext, rw, simp_rw")
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
