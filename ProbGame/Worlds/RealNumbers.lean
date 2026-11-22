import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Balance" =>

%%%
htmlSplit := .never
%%%

:::en
When does a coin that waits leave `coin p` as it is? When what flows from `false` to `true` is what flows back: a balance, $`(1 - p) r = p (1 - q)`. To use such an equation one computes with a minus, and masses cannot: they are numbers in $`[0, \infty]`, where a minus does not undo a plus. So this world takes the masses to the real numbers, computes there, and comes back with the balance; in *Hypergeometric* it is used again. In Lean only.
:::

:::de
Wann lässt eine Münze, die wartet, `coin p`, wie es ist? Wenn das, was von `false` nach `true` fließt, gleich dem ist, was zurückfließt: ein Gleichgewicht, $`(1 - p) r = p (1 - q)`. Um so eine Gleichung zu benutzen, rechnet man mit einem Minus, und Massen können das nicht: Sie sind Zahlen in $`[0, \infty]`, wo ein Minus kein Plus rückgängig macht. Also bringt diese Welt die Massen zu den reellen Zahlen, rechnet dort und kommt mit dem Gleichgewicht zurück; in *Hypergeometrisch* wird es wieder gebraucht. Nur in Lean.
:::

::::leanonly (proof := "(p : I) : (↑p : ℝ≥0∞) = ENNReal.ofReal (p : ℝ)") (lemma := "mass_eq_ofReal") (uses := "-")
:::en
*A mass is a real number.* Masses live in $`[0, \infty]` (`ℝ≥0∞`): there is no minus there that would undo a plus, and `ring` cannot use $`p + (1 - p) = 1`. Real numbers (`ℝ`) can. The way there: `↑p` is the real number $`p`, made a mass by `ENNReal.ofReal`.
:::

:::de
*Eine Masse ist eine reelle Zahl.* Massen leben in $`[0, \infty]` (`ℝ≥0∞`): Dort gibt es kein Minus, das ein Plus rückgängig macht, und `ring` kann $`p + (1 - p) = 1` nicht benutzen. Reelle Zahlen (`ℝ`) können das. Der Weg dorthin: `↑p` ist die reelle Zahl $`p`, durch `ENNReal.ofReal` zur Masse gemacht.
:::

:::proofen
By definition: `rfl`. (Two arrows, two meanings: in `(p : ℝ)` the number $`p` of $`[0, 1]` as a real number, in `(↑p : ℝ≥0∞)` as a mass.)
:::

:::proofde
Nach Definition: `rfl`. (Zwei Pfeile, zwei Bedeutungen: in `(p : ℝ)` die Zahl $`p` aus $`[0, 1]` als reelle Zahl, in `(↑p : ℝ≥0∞)` als Masse.)
:::
:::solution
```
rfl
```
:::
::::

::::leanonly (proof := "(p q : I) : (↑p * ↑q : ℝ≥0∞) = ENNReal.ofReal ((p : ℝ) * q)") (new := "mass_mul_real") (uses := "mass_mul_real")
:::en
*Products.* A product of masses is the mass of the product of the real numbers.
:::

:::de
*Produkte.* Ein Produkt von Massen ist die Masse des Produkts der reellen Zahlen.
:::

:::proofen
`mass_mul_real : ↑p * ↑q = ENNReal.ofReal (p * q)`.
:::

:::proofde
`mass_mul_real : ↑p * ↑q = ENNReal.ofReal (p * q)`.
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
:::

:::proofde
`ENNReal.ofReal_add (ha : 0 ≤ a) (hb : 0 ≤ b) : ENNReal.ofReal (a + b) = ENNReal.ofReal a + ENNReal.ofReal b`, hier rückwärts (`←`). Die zwei Bedingungen kommen in die Klammern: `real_mul_nonneg p q : 0 ≤ p * q` (ein Produkt von Zahlen aus $`[0, 1]`).
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

::::leanonly (proof := "(p q r : ℝ) (h : (1 - p) * r = p * (1 - q)) : p * q + (1 - p) * r = p") (lemma := "balance") (uses := "-")
:::en
*Computing with a hypothesis.* The goal follows from `h` by computing: add `h` to it, and both sides agree.
:::

:::de
*Rechnen mit einer Annahme.* Das Ziel folgt aus `h` durch Rechnen: Zähl `h` dazu, und beide Seiten stimmen überein.
:::

:::proofen
Now with `h` once: `linear_combination h`. What you prove is unlocked as `balance`.
:::

:::proofde
Jetzt mit `h` einmal: `linear_combination h`. Was du beweist, wird als `balance` freigeschaltet.
:::
:::solution
```
linear_combination h
```
:::
::::

:::::leanonly (proof := "(a b : ℝ) (h : a + b = 1) (k : a = 2 * b) : a = ⟦2/3 ‖ 1/3, 1/2, 2/3⟧") (uses := "-")
::::hint (anchor := "gap")
:::en
At `true` twice as much as at `false`, and together one.
:::

:::de
Bei `true` doppelt so viel wie bei `false`, und zusammen eins.
:::
::::

:::en
*Two hypotheses.* A coin with mass $`a` at `true` and $`b` at `false`: together one (`h`), and at `true` twice as much as at `false` (`k`). How much lies at `true`?
:::

:::de
*Zwei Annahmen.* Eine Münze mit Masse $`a` bei `true` und $`b` bei `false`: zusammen eins (`h`), und bei `true` doppelt so viel wie bei `false` (`k`). Wie viel liegt bei `true`?
:::

:::proofen
To get rid of $`b`: twice `h` plus `k` is $`3a + 2b = 2 + 2b`, that is $`3a = 2`. A third of it is the goal; `linear_combination` takes such a sum of hypotheses.

*Tip.* `linear_combination (2 * h + k) / 3`.
:::

:::proofde
Um $`b` loszuwerden: Zweimal `h` plus `k` ist $`3a + 2b = 2 + 2b`, also $`3a = 2`. Ein Drittel davon ist das Ziel; `linear_combination` nimmt so eine Summe von Annahmen.

*Tipp.* `linear_combination (2 * h + k) / 3`.
:::
:::solution
```
linear_combination (2 * h + k) / 3
```
:::
:::::

:::::leanonly (proof := "(a b : ℝ) (h : a + b ≠ 0) : a / (a + b) + b / (a + b) = ⟦1 ‖ 1, a + b, 1 / (a + b)⟧") (new := "field_simp") (uses := "-")
::::hint (anchor := "item:field_simp")
:::en
`field_simp`: an equation between fractions, multiplied by its denominators.
:::

:::de
`field_simp`: eine Gleichung zwischen Brüchen, mit ihren Nennern multipliziert.
:::
::::

:::en
*Shares.* Two amounts $`a` and $`b`: the share of $`a` in the whole, and the share of $`b`. What are they together?
:::

:::de
*Anteile.* Zwei Mengen $`a` und $`b`: der Anteil von $`a` am Ganzen und der Anteil von $`b`. Was sind sie zusammen?
:::

:::proofen
An equation between fractions: the new tactic `field_simp` multiplies it by its denominators. It may do so, since they are not $`0`: that is `h`, and `field_simp` finds it by itself.

*Tip.* `field_simp`.
:::

:::proofde
Eine Gleichung zwischen Brüchen: Die neue Taktik `field_simp` multipliziert sie mit ihren Nennern. Das darf sie, weil sie nicht $`0` sind: Das ist `h`, und `field_simp` findet es selbst.

*Tipp.* `field_simp`.
:::
:::solution
```
field_simp
```
:::
:::::

:::::leanonly (proof := "(p q r : ℝ) (h : r + 1 - q ≠ 0) (hp : p = ⟦r / (r + 1 - q) ‖ r / (r + 1 - q), r / (1 - q), (1 - q) / (r + 1 - q)⟧) : (1 - p) * r = p * (1 - q)") (uses := "-")
::::hint (anchor := "gap")
:::en
Solve the balance $`(1 - p) r = p (1 - q)` for $`p`.
:::

:::de
Löse das Gleichgewicht $`(1 - p) r = p (1 - q)` nach $`p` auf.
:::
::::

:::en
*Which coin is in balance?* From `true` the chain goes on with `coin q`, from `false` with `coin r`. For which $`p` is what flows to `true`, $`(1 - p) r`, what flows back, $`p (1 - q)`?
:::

:::de
*Welche Münze ist im Gleichgewicht?* Von `true` geht die Kette mit `coin q` weiter, von `false` mit `coin r`. Für welches $`p` ist das, was nach `true` fließt, $`(1 - p) r`, gleich dem, was zurückfließt, $`p (1 - q)`?
:::

:::proofen
`hp` is a hypothesis, a rule of this level: `rw [hp]` puts the value in for $`p`. What is left is an equation between fractions, and then a computation.
:::

:::proofde
`hp` ist eine Annahme, eine Regel dieses Levels: `rw [hp]` setzt den Wert für $`p` ein. Übrig bleibt eine Gleichung zwischen Brüchen, und dann eine Rechnung.
:::
:::solution
```
rw [hp]
field_simp
ring
```
:::
:::::

::::leanonly (proof := "(p q r : I) (h : (1 - (p : ℝ)) * r = p * (1 - q)) : (do let x ← coin p; bif x then coin q else coin r) = coin p") (lemma := "coin_stays") (uses := "bool_ext, bind_true, mass_mul_real, ENNReal.ofReal_add, real_mul_nonneg, symm_real, mass_eq_ofReal, balance, bind_false")
:::en
*Boss: a balance that stays.* The chain of *Coins that Wait*: from `true` to `coin q`, from `false` to `coin r`. `coin p` stays when what flows from `false` to `true`, $`(1 - p) r`, is what flows back, $`p (1 - q)`: a balance.
:::

:::de
*Endgegner: ein Gleichgewicht, das bleibt.* Die Kette aus *Münzen, die warten*: von `true` zu `coin q`, von `false` zu `coin r`. `coin p` bleibt, wenn das, was von `false` nach `true` fließt, $`(1 - p) r`, gleich dem ist, was zurückfließt, $`p (1 - q)`: ein Gleichgewicht.
:::
:::solution
```
apply bool_ext
rw [bind_true]
simp
rw [mass_mul_real, mass_mul_real, ← ENNReal.ofReal_add (real_mul_nonneg p q) (real_mul_nonneg (σ p) r), symm_real, mass_eq_ofReal]
congr
apply balance
exact h
```
:::
::::
