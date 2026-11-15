import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Real Numbers" =>

%%%
htmlSplit := .never
%%%

:::en
Masses are numbers in $`[0, \infty]`; there a minus does not undo a plus, and one cannot solve for $`p`. This world is the change to the real numbers: what it takes, and why it is worth it. In Lean only.
:::

:::de
Massen sind Zahlen in $`[0, \infty]`; dort macht ein Minus kein Plus rückgängig, und man kann nicht nach $`p` auflösen. Diese Welt ist der Wechsel zu den reellen Zahlen: was er kostet, und warum er sich lohnt. Nur in Lean.
:::

::::leanonly (proof := "(p : I) : (↑p : ENNReal) = ENNReal.ofReal (p : ℝ)") (lemma := "mass_eq_ofReal") (uses := "-")
:::en
*A mass is a real number.* Masses live in $`[0, \infty]` (`ENNReal`): there is no minus there that would undo a plus, and `ring` cannot use $`p + (1 - p) = 1`. Real numbers (`ℝ`) can. The way there: `↑p` is the real number $`p`, made a mass by `ENNReal.ofReal`.
:::

:::de
*Eine Masse ist eine reelle Zahl.* Massen leben in $`[0, \infty]` (`ENNReal`): Dort gibt es kein Minus, das ein Plus rückgängig macht, und `ring` kann $`p + (1 - p) = 1` nicht benutzen. Reelle Zahlen (`ℝ`) können das. Der Weg dorthin: `↑p` ist die reelle Zahl $`p`, durch `ENNReal.ofReal` zur Masse gemacht.
:::

:::proofen
By definition: `rfl`. (Two arrows, two meanings: in `(p : ℝ)` the number $`p` of $`[0, 1]` as a real number, in `(↑p : ENNReal)` as a mass.)

*Tip.* `rfl`.
:::

:::proofde
Nach Definition: `rfl`. (Zwei Pfeile, zwei Bedeutungen: in `(p : ℝ)` die Zahl $`p` aus $`[0, 1]` als reelle Zahl, in `(↑p : ENNReal)` als Masse.)

*Tipp.* `rfl`.
:::
:::solution
```
rfl
```
:::
::::

::::leanonly (proof := "(p q : I) : (↑p * ↑q : ENNReal) = ENNReal.ofReal ((p : ℝ) * q)") (new := "mass_mul_real") (uses := "mass_mul_real")
:::en
*Products.* A product of masses is the mass of the product of the real numbers.
:::

:::de
*Produkte.* Ein Produkt von Massen ist die Masse des Produkts der reellen Zahlen.
:::

:::proofen
`mass_mul_real : ↑p * ↑q = ENNReal.ofReal (p * q)`.

*Tip.* `rw [mass_mul_real]`.
:::

:::proofde
`mass_mul_real : ↑p * ↑q = ENNReal.ofReal (p * q)`.

*Tipp.* `rw [mass_mul_real]`.
:::
:::solution
```
rw [mass_mul_real]
```
:::
::::

::::leanonly (proof := "(p q r s : I) : ENNReal.ofReal ((p : ℝ) * q) + ENNReal.ofReal ((r : ℝ) * s) = ENNReal.ofReal ((p : ℝ) * q + r * s)") (new := "ENNReal.ofReal_add, real_mul_nonneg") (uses := "ENNReal.ofReal_add, real_mul_nonneg")
:::en
*Sums, with a condition.* `ENNReal.ofReal` turns a negative number into $`0`; so a sum goes through it only when both summands are $`\ge 0`. That is the hard part of the change: the conditions.
:::

:::de
*Summen, mit einer Bedingung.* `ENNReal.ofReal` macht aus einer negativen Zahl $`0`; deshalb geht eine Summe nur hindurch, wenn beide Summanden $`\ge 0` sind. Das ist das Schwierige am Wechsel: die Bedingungen.
:::

:::proofen
`ENNReal.ofReal_add (ha : 0 ≤ a) (hb : 0 ≤ b) : ENNReal.ofReal (a + b) = ENNReal.ofReal a + ENNReal.ofReal b`, here backwards (`←`). The two conditions go into the brackets: `real_mul_nonneg p q : 0 ≤ p * q` (a product of numbers in $`[0, 1]`).

*Tip.* `rw [← ENNReal.ofReal_add (real_mul_nonneg p q) (real_mul_nonneg r s)]`.
:::

:::proofde
`ENNReal.ofReal_add (ha : 0 ≤ a) (hb : 0 ≤ b) : ENNReal.ofReal (a + b) = ENNReal.ofReal a + ENNReal.ofReal b`, hier rückwärts (`←`). Die zwei Bedingungen kommen in die Klammern: `real_mul_nonneg p q : 0 ≤ p * q` (ein Produkt von Zahlen aus $`[0, 1]`).

*Tipp.* `rw [← ENNReal.ofReal_add (real_mul_nonneg p q) (real_mul_nonneg r s)]`.
:::
:::solution
```
rw [← ENNReal.ofReal_add (real_mul_nonneg p q) (real_mul_nonneg r s)]
```
:::
::::

::::leanonly (proof := "(p : I) : (p : ℝ) + (σ p : I) = 1") (new := "symm_real, ring") (uses := "symm_real")
:::en
*1 − p, really.* In `ℝ`, `σ p` is really $`1 - p`, and now computing knows that $`p + (1 - p) = 1`.
:::

:::de
*1 − p, wirklich.* In `ℝ` ist `σ p` wirklich $`1 - p`, und jetzt weiß das Rechnen, dass $`p + (1 - p) = 1`.
:::

:::proofen
`symm_real : ↑(σ p) = 1 - ↑p` (as real numbers), then `ring`: it proves an equation that holds by computing with `+`, `-`, `*`.

*Tip.* `rw [symm_real]`, `ring`.
:::

:::proofde
`symm_real : ↑(σ p) = 1 - ↑p` (als reelle Zahlen), dann `ring`: Es beweist eine Gleichung, die durch Rechnen mit `+`, `-`, `*` gilt.

*Tipp.* `rw [symm_real]`, `ring`.
:::
:::solution
```
rw [symm_real]
ring
```
:::
::::

::::leanonly (proof := "(x y : ℝ) (h : x - y = 2) : 2 * x = 2 * y + 4") (new := "linear_combination") (uses := "-")
:::en
*Twice a hypothesis.* From $`x - y = 2` follows $`2x = 2y + 4`: take the hypothesis twice. In the real numbers that is computing, and a tactic does it.
:::

:::de
*Zweimal eine Annahme.* Aus $`x - y = 2` folgt $`2x = 2y + 4`: Nimm die Annahme zweimal. In den reellen Zahlen ist das Rechnen, und eine Taktik erledigt es.
:::

:::proofen
`linear_combination 2 * h`: the goal, left minus right, is twice `h`, left minus right; `ring` checks it. Without the `2` it fails: try it.

*Tip.* `linear_combination 2 * h`.
:::

:::proofde
`linear_combination 2 * h`: Das Ziel, links minus rechts, ist zweimal `h`, links minus rechts; `ring` prüft es. Ohne die `2` scheitert es: Probier es aus.

*Tipp.* `linear_combination 2 * h`.
:::
:::solution
```
linear_combination 2 * h
```
:::
::::

::::leanonly (proof := "(p q r : ℝ) (h : (1 - p) * r = p * (1 - q)) : p * q + (1 - p) * r = p") (uses := "-")
:::en
*Computing with a hypothesis.* The goal follows from `h` by computing: add `h` to it, and both sides agree.
:::

:::de
*Rechnen mit einer Annahme.* Das Ziel folgt aus `h` durch Rechnen: Zähl `h` dazu, und beide Seiten stimmen überein.
:::

:::proofen
Now with `h` once: `linear_combination h`.

*Tip.* `linear_combination h`.
:::

:::proofde
Jetzt mit `h` einmal: `linear_combination h`.

*Tipp.* `linear_combination h`.
:::
:::solution
```
linear_combination h
```
:::
::::

::::leanonly (proof := "(p q r : I) (h : (1 - (p : ℝ)) * r = p * (1 - q)) : (do let x ← coin p; bif x then coin q else coin r) = coin p") (lemma := "coin_stays") (uses := "bool_ext, bind_true, Bool.cond_true, Bool.cond_false, coin_true, coin_false, mass_mul_real, ENNReal.ofReal_add, real_mul_nonneg, symm_real, mass_eq_ofReal, bind_false")
:::en
*Boss: a balance that stays.* The chain of *Coins that Wait*: from `true` to `coin q`, from `false` to `coin r`. `coin p` stays when what flows from `false` to `true`, $`(1 - p) r`, is what flows back, $`p (1 - q)`: a balance.
:::

:::de
*Endgegner: ein Gleichgewicht, das bleibt.* Die Kette aus *Münzen, die warten*: von `true` zu `coin q`, von `false` zu `coin r`. `coin p` bleibt, wenn das, was von `false` nach `true` fließt, $`(1 - p) r`, gleich dem ist, was zurückfließt, $`p (1 - q)`: ein Gleichgewicht.
:::

:::proofen
As in *A distribution that stays* down to the masses; then everything into `ℝ`: the products, the sum (with its conditions), $`1 - p`, and `↑p` itself (`mass_eq_ofReal`). Now both sides are `ENNReal.ofReal` of something: `congr 1` leaves the real equation, and `linear_combination h`.

*Tip.* `apply bool_ext`, `rw [bind_true, Bool.cond_true, Bool.cond_false]`, `rw [coin_true, coin_true, coin_true, coin_false]`, `rw [mass_mul_real, mass_mul_real, ← ENNReal.ofReal_add (real_mul_nonneg p q) (real_mul_nonneg (σ p) r), symm_real, mass_eq_ofReal]`, `congr 1`, `linear_combination h`.
:::

:::proofde
Wie in *Eine Verteilung, die bleibt* bis zu den Massen; dann alles nach `ℝ`: die Produkte, die Summe (mit ihren Bedingungen), $`1 - p`, und `↑p` selbst (`mass_eq_ofReal`). Jetzt sind beide Seiten `ENNReal.ofReal` von etwas: `congr 1` lässt die reelle Gleichung, und `linear_combination h`.

*Tipp.* `apply bool_ext`, `rw [bind_true, Bool.cond_true, Bool.cond_false]`, `rw [coin_true, coin_true, coin_true, coin_false]`, `rw [mass_mul_real, mass_mul_real, ← ENNReal.ofReal_add (real_mul_nonneg p q) (real_mul_nonneg (σ p) r), symm_real, mass_eq_ofReal]`, `congr 1`, `linear_combination h`.
:::
:::solution
```
apply bool_ext
rw [bind_true, Bool.cond_true, Bool.cond_false]
rw [coin_true, coin_true, coin_true, coin_false]
rw [mass_mul_real, mass_mul_real, ← ENNReal.ofReal_add (real_mul_nonneg p q) (real_mul_nonneg (σ p) r), symm_real, mass_eq_ofReal]
congr 1
linear_combination h
```
:::
::::
