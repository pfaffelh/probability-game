import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Balance" =>

%%%
htmlSplit := .never
%%%

:::en
When does a second stage leave `coin p` as it is? When what flows from `false` to `true` is what flows back: a balance, $`(1 - p) r = p (1 - q)`. To use such an equation one computes with a minus, and masses cannot: they are numbers in $`[0, \infty]`, where a minus does not undo a plus. So this world takes the masses to the real numbers, computes there, and comes back with the balance; in *Hypergeometric* it is used again. In Lean only.
:::

:::de
Wann lässt eine zweite Stufe `coin p`, wie es ist? Wenn das, was von `false` nach `true` fließt, gleich dem ist, was zurückfließt: ein Gleichgewicht, $`(1 - p) r = p (1 - q)`. Um so eine Gleichung zu benutzen, rechnet man mit einem Minus, und Massen können das nicht: Sie sind Zahlen in $`[0, \infty]`, wo ein Minus kein Plus rückgängig macht. Also bringt diese Welt die Massen zu den reellen Zahlen, rechnet dort und kommt mit dem Gleichgewicht zurück; in *Hypergeometrisch* wird es wieder gebraucht. Nur in Lean.
:::

::::leanonly (proof := "(p : I) : (↑p : ℝ≥0∞) = ENNReal.ofReal (p : ℝ)") (lemma := "mass_eq_ofReal") (uses := "rfl")
:::en
*A mass is a real number.* Masses live in $`[0, \infty]` (`ℝ≥0∞`): there is no minus there that would undo a plus, and `ring` cannot use $`p + (1 - p) = 1`. Real numbers (`ℝ`) can. The way there: `↑p` is the real number $`p`, made a mass by `ENNReal.ofReal`.
:::

:::de
*Eine Masse ist eine reelle Zahl.* Massen leben in $`[0, \infty]` (`ℝ≥0∞`): Dort gibt es kein Minus, das ein Plus rückgängig macht, und `ring` kann $`p + (1 - p) = 1` nicht benutzen. Reelle Zahlen (`ℝ`) können das. Der Weg dorthin: `↑p` ist die reelle Zahl $`p`, durch `ENNReal.ofReal` zur Masse gemacht.
:::

:::proofen
By definition. (Two arrows, two meanings: in `(p : ℝ)` the number $`p` of $`[0, 1]` as a real
number, in `(↑p : ℝ≥0∞)` as a mass.)
:::

:::proofde
Nach Definition. (Zwei Pfeile, zwei Bedeutungen: in `(p : ℝ)` die Zahl $`p` aus $`[0, 1]` als reelle
Zahl, in `(↑p : ℝ≥0∞)` als Masse.)
:::
:::solution
```
rfl
```
:::
::::

::::leanonly (proof := "(p q : I) : (↑p * ↑q : ℝ≥0∞) = ENNReal.ofReal ((p : ℝ) * q)") (new := "mass_mul_real") (uses := "mass_mul_real, mass_mul, exact, rfl, rw")
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
:::solution
```
rw [← mass_mul]
rfl
```
:::
:::solution
```
exact mass_mul_real p q
```
:::
::::

::::leanonly (proof := "(p q r s : I) : ENNReal.ofReal ((p : ℝ) * q) + ENNReal.ofReal ((r : ℝ) * s) = ENNReal.ofReal ((p : ℝ) * q + r * s)") (new := "ENNReal.ofReal_add, real_mul_nonneg") (uses := "ENNReal.ofReal_add, real_mul_nonneg, <;>, apply, rw")
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
:::solution
```
rw [ENNReal.ofReal_add (real_mul_nonneg p q) (real_mul_nonneg r s)]
```
:::
:::solution
```
rw [← ENNReal.ofReal_add]
apply real_mul_nonneg
apply real_mul_nonneg
```
:::
:::solution
```
rw [ENNReal.ofReal_add] <;> apply real_mul_nonneg
```
:::
::::

::::leanonly (proof := "(p : I) : (p : ℝ) + (σ p : I) = 1") (new := "symm_real, ring") (uses := "symm_real, ring, rw")
:::en
*1 − p, really.* In `ℝ`, `σ p` is really $`1 - p`, and now computing knows that $`p + (1 - p) = 1`.
:::

:::de
*1 − p, wirklich.* In `ℝ` ist `σ p` wirklich $`1 - p`, und jetzt weiß das Rechnen, dass $`p + (1 - p) = 1`.
:::

:::proofen
`symm_real : ↑(σ p) = 1 - ↑p` (as real numbers). What is left holds by computing with `+`, `-`, `*`.
:::

:::proofde
`symm_real : ↑(σ p) = 1 - ↑p` (als reelle Zahlen). Was bleibt, gilt durch Rechnen mit `+`, `-`, `*`.
:::
:::solution
```
rw [symm_real]
ring
```
:::
::::

::::leanonly (proof := "(x y : ℝ) (h : x - y = 2) : 2 * x = 2 * y + 4") (new := "linear_combination") (uses := "linear_combination")
:::en
*Twice a hypothesis.* From $`x - y = 2` follows $`2x = 2y + 4`: take the hypothesis twice. In the real numbers that is computing, and a tactic does it.
:::

:::de
*Zweimal eine Annahme.* Aus $`x - y = 2` folgt $`2x = 2y + 4`: Nimm die Annahme zweimal. In den reellen Zahlen ist das Rechnen, und eine Taktik erledigt es.
:::

:::proofen
The new tactic `linear_combination e`: the goal follows from the hypotheses in `e` by computing.
With `e = c * h`: the goal, left minus right, is `c` times `h`, left minus right; `ring` checks it.
Which `c`? With `1` it fails: try it.
:::

:::proofde
Die neue Taktik `linear_combination e`: Das Ziel folgt durch Rechnen aus den Annahmen in `e`. Mit
`e = c * h`: Das Ziel, links minus rechts, ist `c`-mal `h`, links minus rechts; `ring` prüft es.
Welches `c`? Mit `1` scheitert es: Probier es aus.
:::
:::solution
```
linear_combination 2 * h
```
:::
::::

::::leanonly (proof := "(p q r : ℝ) (h : (1 - p) * r = p * (1 - q)) : p * q + (1 - p) * r = p") (lemma := "balance") (uses := "linear_combination, ring, rw")
:::en
*Computing with a hypothesis.* The goal follows from `h` by computing: add `h` to it, and both sides agree.
:::

:::de
*Rechnen mit einer Annahme.* Das Ziel folgt aus `h` durch Rechnen: Zähl `h` dazu, und beide Seiten stimmen überein.
:::

:::proofen
Now `h` once is enough. What you prove is unlocked as `balance`.
:::

:::proofde
Jetzt reicht `h` einmal. Was du beweist, wird als `balance` freigeschaltet.
:::
:::solution
```
linear_combination h
```
:::
:::solution
```
rw [h]
ring
```
:::
::::

:::::leanonly (proof := "(a b : ℝ) (h : a + b = 1) (k : a = 2 * b) : a = ⟦2/3 ‖ 1/3, 1/2, 2/3⟧") (new := "linarith") (uses := "linarith, linear_combination, rw")
::::hint (anchor := "item:linarith")
:::en
`linarith` finds the factors by itself.
:::

:::de
`linarith` findet die Faktoren selbst.
:::
::::

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
Two hypotheses: `linear_combination` also takes a sum of them, such as `(c * h + d * k) / e`. Which
sum gets rid of $`b`?
:::

:::proofde
Zwei Annahmen: `linear_combination` nimmt auch eine Summe davon, etwa `(c * h + d * k) / e`. Welche
Summe wird $`b` los?
:::
:::solution
```
linear_combination (2 * h + k) / 3
```
:::
:::solution
```
linarith
```
:::
:::solution
```
rw [k] at h
rw [k]
linear_combination 2 * h / 3
```
:::
:::::

:::::leanonly (proof := "(a b : ℝ) (h : a + b ≠ 0) : a / (a + b) + b / (a + b) = ⟦1 ‖ 1, a + b, 1 / (a + b)⟧") (new := "field_simp") (uses := "field_simp")
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
:::

:::proofde
Eine Gleichung zwischen Brüchen: Die neue Taktik `field_simp` multipliziert sie mit ihren Nennern. Das darf sie, weil sie nicht $`0` sind: Das ist `h`, und `field_simp` findet es selbst.
:::
:::solution
```
field_simp
```
:::
:::::

:::::leanonly (proof := "(p q r : ℝ) (h : r + 1 - q ≠ 0) (hp : p = ⟦r / (r + 1 - q) ‖ r / (r + 1 - q), r / (1 - q), (1 - q) / (r + 1 - q)⟧) : (1 - p) * r = p * (1 - q)") (new := "subst") (uses := "field_simp, linarith, ring, rw, subst")
::::hint (anchor := "item:subst")
:::en
`subst hp` puts the right side of `hp` for `p` everywhere.
:::

:::de
`subst hp` setzt überall die rechte Seite von `hp` für `p` ein.
:::
::::

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
`hp` is a hypothesis, a rule of this level. What is left is an equation between fractions, and then
a computation.
:::

:::proofde
`hp` ist eine Annahme, eine Regel dieses Levels. Übrig bleibt eine Gleichung zwischen Brüchen, und
dann eine Rechnung.
:::
:::solution
```
rw [hp]
field_simp
ring
```
:::
:::solution
```
subst hp
field_simp
ring
```
:::
:::solution
```
rw [hp]
field_simp
linarith
```
:::
:::::

::::leanonly (proof := "(p q r : I) (h : (1 - (p : ℝ)) * r = p * (1 - q)) : (do let x ← coin p; bif x then coin q else coin r) = coin p") (lemma := "coin_stays") (uses := "bool_ext, bind_true, mass_mul_real, ENNReal.ofReal_add, real_mul_nonneg, symm_real, mass_eq_ofReal, balance, eq_coin, apply, congr, exact, linarith, rw, simp")
:::en
*Boss: a balance that stays.* The chain of *Multi-Stage Experiments*: from `true` to `coin q`, from `false` to `coin r`. `coin p` stays when what flows from `false` to `true`, $`(1 - p) r`, is what flows back, $`p (1 - q)`: a balance.
:::

:::de
*Endgegner: ein Gleichgewicht, das bleibt.* Die Kette aus *Mehrstufige Experimente*: von `true` zu `coin q`, von `false` zu `coin r`. `coin p` bleibt, wenn das, was von `false` nach `true` fließt, $`(1 - p) r`, gleich dem ist, was zurückfließt, $`p (1 - q)`: ein Gleichgewicht.
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
:::solution
```
apply bool_ext
rw [bind_true]
simp
rw [mass_mul_real, mass_mul_real, ← ENNReal.ofReal_add (real_mul_nonneg p q) (real_mul_nonneg (σ p) r), symm_real, mass_eq_ofReal]
congr
linarith
```
:::
:::solution
```
apply eq_coin
rw [bind_true]
simp
rw [mass_mul_real, mass_mul_real, ← ENNReal.ofReal_add (real_mul_nonneg p q) (real_mul_nonneg (σ p) r), symm_real, mass_eq_ofReal]
congr
apply balance
exact h
```
:::
:::solution
```
apply bool_ext
rw [bind_true]
simp
rw [mass_mul_real, mass_mul_real, ← ENNReal.ofReal_add (real_mul_nonneg p q) (real_mul_nonneg (σ p) r), symm_real, balance h, mass_eq_ofReal]
```
:::
::::
