import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "ENNReal" =>

%%%
htmlSplit := .never
number := false
%%%

:::en
Masses are numbers in $`[0, \infty]`, in Lean `ℝ≥0∞` (`ENNReal`): never negative, and $`\infty` is
one of them. Most rules are those of the numbers you know. Two are different: taking away stops at
$`0` ($`a - b = 0` when $`b \ge a`), and $`\infty` swallows ($`\infty + a = \infty`). This world
practises the rules that the next worlds compute with.
:::

:::de
Massen sind Zahlen in $`[0, \infty]`, in Lean `ℝ≥0∞` (`ENNReal`): nie negativ, und $`\infty` gehört
dazu. Die meisten Regeln sind die der Zahlen, die du kennst. Zwei sind anders: Abziehen hört bei $`0`
auf ($`a - b = 0`, wenn $`b \ge a`), und $`\infty` verschluckt ($`\infty + a = \infty`). Diese Welt
übt die Regeln, mit denen die nächsten Welten rechnen.
:::

::::leanonly (proof := "(a b : ℝ≥0∞) : 0 + (a + b) = b + a") (new := "zero_add, add_comm") (uses := "zero_add, add_comm, add_zero, mul_zero, add_assoc, rw")
:::en
*Adding.* Two rules to start: `zero_add : 0 + a = a` and `add_comm : a + b = b + a`.
:::

:::de
*Addieren.* Zwei Regeln zum Anfang: `zero_add : 0 + a = a` und `add_comm : a + b = b + a`.
:::

:::proofen
`rw [zero_add]` puts `a + b` in the place of `0 + (a + b)`: the `a` of the rule stands for `a + b`
here.
:::

:::proofde
`rw [zero_add]` setzt `a + b` an die Stelle von `0 + (a + b)`: Das `a` der Regel steht hier für
`a + b`.
:::
:::solution
```
rw [zero_add, add_comm]
```
:::
:::solution
```
rw [zero_add]
rw [add_comm]
```
:::
:::solution
```
rw [add_comm b a, zero_add]
```
:::
::::

::::leanonly (proof := "(a : ℝ≥0∞) : a + 0 = ⟦a ‖ a, 0⟧") (lemma := "add_zero") (uses := "add_comm, zero_add, add_assoc, add_zero, mul_zero, rw")
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
::::

:::::leanonly (proof := "(a b c : ℝ≥0∞) : a + (b + c) = c + (a + b)") (new := "add_assoc") (uses := "add_assoc, add_comm, add_right_comm, rw")
:::en
*Brackets.* `a + b + c` means `(a + b) + c`, and `add_assoc : a + b + c = a + (b + c)` moves the
brackets.
:::

:::de
*Klammern.* `a + b + c` heißt `(a + b) + c`, und `add_assoc : a + b + c = a + (b + c)` verschiebt die
Klammern.
:::

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
From right to left, `← add_assoc` puts the brackets to the left; then `add_comm` turns the sum round.
:::

:::proofde
Von rechts nach links setzt `← add_assoc` die Klammern nach links; dann dreht `add_comm` die Summe
um.
:::
:::solution
```
rw [← add_assoc, add_comm]
```
:::
:::solution
```
rw [← add_assoc]
rw [add_comm]
```
:::
:::solution
```
rw [add_comm c, add_assoc]
```
:::
:::::

::::leanonly (proof := "(a : ℝ≥0∞) : 1 * a = ⟦a ‖ a, 1, 0⟧") (lemma := "one_mul") (new := "mul_one, mul_comm") (uses := "mul_comm, mul_one, one_mul, rw")
:::en
*One times.* Multiplying: you get `mul_one : a * 1 = a` and `mul_comm : a * b = b * a`; the one on the
left is yours to prove.
:::

:::de
*Eins mal.* Multiplizieren: Du bekommst `mul_one : a * 1 = a` und `mul_comm : a * b = b * a`; die Eins
links beweist du selbst.
:::

:::proofen
Your result becomes the lemma `one_mul`.
:::

:::proofde
Dein Ergebnis wird das Lemma `one_mul`.
:::
:::solution
```
rw [mul_comm, mul_one]
```
:::
:::solution
```
rw [mul_comm]
rw [mul_one]
```
:::
::::

::::leanonly (proof := "(a : ℝ≥0∞) : 0 * a = ⟦0 ‖ a, 1, 0⟧") (lemma := "zero_mul") (new := "mul_zero") (uses := "mul_comm, mul_zero, zero_add, rw")
:::en
*Zero times.* The same with `0`: you get `mul_zero : a * 0 = 0`.
:::

:::de
*Null mal.* Dasselbe mit `0`: Du bekommst `mul_zero : a * 0 = 0`.
:::

:::proofen
Your result becomes the lemma `zero_mul`.
:::

:::proofde
Dein Ergebnis wird das Lemma `zero_mul`.
:::
:::solution
```
rw [mul_comm, mul_zero]
```
:::
:::solution
```
rw [mul_comm]
rw [mul_zero]
```
:::
::::

::::leanonly (proof := "(a b c d : ℝ≥0∞) : (a + b) * (c + d) = a * c + a * d + (b * c + b * d)") (new := "add_mul, mul_add") (uses := "add_mul, mul_add, rw")
:::en
*Multiplying out.* `add_mul : (a + b) * c = a * c + b * c` and `mul_add : a * (b + c) = a * b + a * c`.
:::

:::de
*Ausmultiplizieren.* `add_mul : (a + b) * c = a * c + b * c` und `mul_add : a * (b + c) = a * b + a * c`.
:::
:::solution
```
rw [add_mul, mul_add, mul_add]
```
:::
:::solution
```
rw [add_mul]
rw [mul_add]
rw [mul_add]
```
:::
::::

:::::leanonly (proof := "(a b : ℝ≥0∞) : ⟦a - a + b ‖ a + b - a, b - a + a, a - a + b⟧ = b") (new := "tsub_self, tsub_zero") (uses := "tsub_self, zero_add, add_zero, mul_zero, rw")
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
:::::

::::leanonly (proof := "(a b : ℝ≥0∞) (h : a ≠ ∞) : a + b - a = b") (new := "ENNReal.add_sub_cancel_left, top_add") (uses := "ENNReal.add_sub_cancel_left, rw")
:::en
*Taking back.* What was added can be taken away again, if it is finite:
`ENNReal.add_sub_cancel_left (h : a ≠ ∞) : a + b - a = b`. For `∞` it fails: `∞` swallows,
`top_add : ∞ + a = ∞`, so `∞ + b - ∞ = ∞ - ∞ = 0`.
:::

:::de
*Zurücknehmen.* Was addiert wurde, kann man wieder abziehen, wenn es endlich ist:
`ENNReal.add_sub_cancel_left (h : a ≠ ∞) : a + b - a = b`. Für `∞` geht es schief: `∞` verschluckt,
`top_add : ∞ + a = ∞`, also `∞ + b - ∞ = ∞ - ∞ = 0`.
:::

:::proofen
`h : a ≠ ∞` is a hypothesis of this level, a rule of this level only. The rule needs it: write it
behind the rule, `ENNReal.add_sub_cancel_left h`; without it, `rw` leaves it as a second goal.
:::

:::proofde
`h : a ≠ ∞` ist eine Annahme dieses Levels, eine Regel nur dieses Levels. Die Regel braucht sie:
Schreib sie hinter die Regel, `ENNReal.add_sub_cancel_left h`; ohne sie lässt `rw` sie als zweites
Ziel übrig.
:::
:::solution
```
rw [ENNReal.add_sub_cancel_left h]
```
:::
::::

:::::leanonly (proof := "(a b : ℝ≥0∞) : a ≤ b + a") (new := "le_self_add, exact") (uses := "add_comm, le_self_add, add_assoc, exact, rw")
::::hint (anchor := "item:exact")
:::en
`exact h`: closes a goal that is exactly `h`.
:::

:::de
`exact h`: schließt ein Ziel, das genau `h` ist.
:::
::::

:::en
*At most.* `≤` on masses: a summand is at most the sum, `le_self_add : a ≤ a + c`.
:::

:::de
*Höchstens.* `≤` bei Massen: Ein Summand ist höchstens die Summe, `le_self_add : a ≤ a + c`.
:::

:::proofen
First turn the sum round. The new tactic `exact h` closes a goal that is exactly `h`.
:::

:::proofde
Dreh zuerst die Summe um. Die neue Taktik `exact h` schließt ein Ziel, das genau `h` ist.
:::
:::solution
```
rw [add_comm]
exact le_self_add
```
:::
:::solution
```
rw [add_comm b a]
exact le_self_add
```
:::
:::::

::::leanonly (proof := "(a : ℝ≥0∞) (h : a ≤ 1) : a ≠ ⟦∞ ‖ 0, 1, ∞⟧") (new := "apply, ne_top_of_le_ne_top, ENNReal.one_ne_top") (uses := "ne_top_of_le_ne_top, ENNReal.one_ne_top, apply, exact")
:::en
*Finite.* What is at most one is finite: one is finite, and below it there is no `∞`.
:::

:::de
*Endlich.* Was höchstens eins ist, ist endlich: Eins ist endlich, und darunter gibt es kein `∞`.
:::

:::proofen
`ne_top_of_le_ne_top : b ≠ ∞ → a ≤ b → a ≠ ∞`. The new tactic `apply h` works backwards: the goal is
the conclusion of `h`, and what `h` still needs becomes the new goal. What `h` needs can also be
given along, `apply h h₁`: here `ENNReal.one_ne_top : 1 ≠ ∞`.
:::

:::proofde
`ne_top_of_le_ne_top : b ≠ ∞ → a ≤ b → a ≠ ∞`. Die neue Taktik `apply h` arbeitet rückwärts: Das
Ziel ist die Folgerung von `h`, und was `h` noch braucht, wird das neue Ziel. Was `h` braucht, kann
man auch gleich mitgeben, `apply h h₁`: hier `ENNReal.one_ne_top : 1 ≠ ∞`.
:::
:::solution
```
apply ne_top_of_le_ne_top ENNReal.one_ne_top
exact h
```
:::
:::solution
```
exact ne_top_of_le_ne_top ENNReal.one_ne_top h
```
:::
:::solution
```
apply ne_top_of_le_ne_top ENNReal.one_ne_top h
```
:::
::::

::::leanonly (proof := "(a b : ℝ≥0∞) (h : a ≠ ∞) : (a + b) * (1 + 0) - 1 * a = 0 + b") (uses := "add_zero, mul_one, one_mul, zero_add, ENNReal.add_sub_cancel_left, mul_zero, rw")
:::en
*Boss: compute.* The rules of this world, one after the other.
:::

:::de
*Endgegner: Rechnen.* Die Regeln dieser Welt, eine nach der anderen.
:::
:::solution
```
rw [add_zero, mul_one, one_mul, zero_add, ENNReal.add_sub_cancel_left h]
```
:::
:::solution
```
rw [add_zero, mul_one]
rw [one_mul, zero_add]
rw [ENNReal.add_sub_cancel_left h]
```
:::
:::solution
```
rw [zero_add, one_mul, add_zero, mul_one]
rw [ENNReal.add_sub_cancel_left h]
```
:::
::::
