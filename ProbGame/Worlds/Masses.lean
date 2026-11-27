import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Masses" =>

%%%
htmlSplit := .never
number := false
%%%

:::en
A coin shows `true` (heads) or `false` (tails); `coin p` is the coin that shows `true` with
probability $`p` and `false` with probability $`1 - p`. A distribution on `Bool` is, in Lean,
`μ : DiscreteMeasure Bool`: it gives each of the two points its *mass*, `μ true` and `μ false`, the
heights of its two bars. The coin with probability $`p` is `(coin p : DiscreteMeasure Bool)`.
:::

:::de
Eine Münze zeigt `true` (Kopf) oder `false` (Zahl); `coin p` ist die Münze, die mit
Wahrscheinlichkeit $`p` `true` zeigt und mit Wahrscheinlichkeit $`1 - p` `false`. Eine Verteilung auf
`Bool` ist in Lean `μ : DiscreteMeasure Bool`: Sie gibt jedem der beiden Punkte seine *Masse*,
`μ true` und `μ false`, die Höhen ihrer beiden Säulen. Die Münze mit Wahrscheinlichkeit $`p` ist
`(coin p : DiscreteMeasure Bool)`.
:::

:::::circuit (height := "400") (inputs := "x") (gates := "") (coins := "p") (target := "bool true:p false:1-p") (context := "Lean/Rules.lean") (proof := "(p : I) : coin p true = p") (lemma := "coin_true") (play := "x>out") (uses := "rfl")
:::en
*The mass at true.* Wire the coin `x` to the output.
:::

:::de
*Die Masse bei true.* Verbinde die Münze `x` mit dem Ausgang.
:::

::::hint (anchor := "input")
:::en
A coin shows `true` (heads) or `false` (tails); `coin p` is the coin that shows `true` with
probability $`p` and `false` with probability $`1 - p`. As a distribution on `Bool` it has two
masses: $`p` at `true` and $`1 - p` at `false`.
:::

:::de
Eine Münze zeigt `true` (Kopf) oder `false` (Zahl); `coin p` ist die Münze, die mit
Wahrscheinlichkeit $`p` `true` zeigt und mit Wahrscheinlichkeit $`1 - p` `false`. Als Verteilung
auf `Bool` hat sie zwei Massen: $`p` bei `true` und $`1 - p` bei `false`.
:::
::::

:::proofen
`(coin p) true` is the mass of the coin at `true`. A distribution is, in Lean, its masses (its *weight* function):

```
structure DiscreteMeasure (α : Type) where
  weight : α → ℝ≥0∞
```

`ℝ≥0∞` (in Lean `ENNReal`) are the numbers from 0 to ∞, ∞ included: a mass is never negative. And the coin is defined by its two masses:

```
def coin (p : I) : DiscreteMeasure Bool where
  weight := fun
    | true => ↑p
    | false => ↑(σ p)
```

`I` is the unit interval $`[0, 1]`, where the probability `p` lies; `σ p` is $`1 - p`, again in
`I`. The arrow `↑` makes a number of `I` a mass in `ℝ≥0∞`. (`μ x` is `μ.weight x`.) So the statement holds by definition. The
statement is the rule `coin_true`; once proved, it is in your inventory.
:::

:::proofde
`(coin p) true` ist die Masse der Münze bei `true`. Eine Verteilung ist in Lean ihre Massen (ihre *Gewichtsfunktion*):

```
structure DiscreteMeasure (α : Type) where
  weight : α → ℝ≥0∞
```

`ℝ≥0∞` (in Lean `ENNReal`) sind die Zahlen von 0 bis ∞, ∞ eingeschlossen: Eine Masse ist nie negativ. Und die Münze ist durch ihre zwei Massen definiert:

```
def coin (p : I) : DiscreteMeasure Bool where
  weight := fun
    | true => ↑p
    | false => ↑(σ p)
```

`I` ist das Einheitsintervall $`[0, 1]`, in dem die Wahrscheinlichkeit `p` liegt; `σ p` ist $`1 - p`,
wieder in `I`. Der Pfeil `↑` macht aus einer Zahl aus `I` eine Masse in `ℝ≥0∞`. (`μ x` ist
`μ.weight x`.) Also gilt die Aussage nach Definition.
Die Aussage ist die Regel `coin_true`; bewiesen, ist sie in deinem Inventar.
:::
:::solution
```
rfl
```
:::
:::::

:::::leanonly (proof := "(p : I) : coin p false = ⟦σ p ‖ p, σ p, 1, 0⟧") (lemma := "coin_false") (uses := "rfl")
::::hint (anchor := "statement")
:::en
`σ p` is $`1 - p`.

Only the type differs: `σ p : I`, but `1 - ↑p : ℝ≥0∞`.
:::

:::de
`σ p` ist $`1 - p`.

Nur der Typ ist ein anderer: `σ p : I`, aber `1 - ↑p : ℝ≥0∞`.
:::
::::

:::en
*The mass at false.* At `false` the coin has the rest, $`1 - p`.
:::

:::de
*Die Masse bei false.* Bei `false` hat die Münze den Rest, $`1 - p`.
:::

:::proofen
`σ p` is $`1 - p`, again in $`I`, and `↑(σ p)` is it as a mass. Again by the definition of `coin` (the line `| false => ↑(σ p)`).
:::

:::proofde
`σ p` ist $`1 - p`, wieder in $`I`, und `↑(σ p)` ist das als Masse. Wieder nach der Definition von `coin` (die Zeile `| false => ↑(σ p)`).
:::
:::solution
```
rfl
```
:::
:::::

:::::leanonly (proof := "(p : I) : coin p true = p ∧ coin p false = σ p") (new := "constructor") (uses := "constructor, rfl")
::::hint (anchor := "item:constructor")
:::en
`constructor`: a goal `A ∧ B` becomes two goals, `A` and `B`.
:::

:::de
`constructor`: Aus einem Ziel `A ∧ B` werden zwei Ziele, `A` und `B`.
:::
::::

:::en
*Both masses.* Two statements in one, joined by `∧` (and): the mass at `true`, and the mass at `false`.
:::

:::de
*Beide Massen.* Zwei Aussagen in einer, verbunden mit `∧` (und): die Masse bei `true` und die Masse bei `false`.
:::

:::proofen
The new tactic `constructor` makes two goals of `A ∧ B`: first `A`, then `B`. Each of them holds by definition, as before.
:::

:::proofde
Die neue Taktik `constructor` macht aus `A ∧ B` zwei Ziele: erst `A`, dann `B`. Jedes gilt nach Definition, wie zuvor.
:::
:::solution
```
constructor
rfl
rfl
```
:::
:::::

::::leanonly (proof := "(p : I) : 0 + coin p true = p") (new := "zero_add") (uses := "zero_add, coin_true, add_zero, mul_zero, coin_false, coin_total, rw, -rfl")
:::en
*Zero plus.* Not every rule is a definition: `zero_add : 0 + a = a` is a rule of arithmetic, given
here (it is proved in Mathlib, not by `rfl`). A rule is used by rewriting with it, with `rw`.
:::

:::de
*Null plus.* Nicht jede Regel ist eine Definition: `zero_add : 0 + a = a` ist eine Rechenregel, hier
gegeben (sie ist in Mathlib bewiesen, nicht mit `rfl`). Eine Regel benutzt man, indem man mit ihr
umschreibt.
:::

:::proofen
A rule `h : a = b` is used with `rw [h]`: it rewrites `a` into `b` in the goal (from right to left
with `←`, later), several at once with `rw [h, k]`. When the goal then reads `x = x`, it is closed.
:::

:::proofde
Eine Regel `h : a = b` benutzt man mit `rw [h]`: Sie schreibt `a` im Ziel zu `b` um (von rechts nach
links mit `←`, später), mehrere auf einmal mit `rw [h, k]`. Lautet das Ziel danach `x = x`, ist es
geschlossen.
:::
:::solution
```
rw [zero_add]
rw [coin_true]
```
:::
::::

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
::::

::::leanonly (proof := "(c : Bool) : (c == true) = ⟦c ‖ c, !c, true⟧") (lemma := "beq_true") (uses := "<;>, cases, rfl")
:::hint (anchor := "none")
:::

:::en
*Equal to true.* `c == b` is `true` when `c` and `b` are equal, else `false`: a test, itself a
`Bool`. Testing `c == true` gives back `c` itself.
:::

:::de
*Gleich true.* `c == b` ist `true`, wenn `c` und `b` gleich sind, sonst `false`: ein Test, selbst ein
`Bool`. Der Test `c == true` gibt `c` selbst zurück.
:::

:::proofen
Two cases, as in *Bool*: `c` is `true` or `false`, and in each Lean computes both sides.
:::

:::proofde
Zwei Fälle, wie in *Bool*: `c` ist `true` oder `false`, und in jedem rechnet Lean beide Seiten
aus.
:::
:::solution
```
cases c <;> rfl
```
:::
::::

:::::leanonly (proof := "(b : Bool) : (true == b) = ⟦b ‖ b, !b, true⟧") (lemma := "Bool.true_beq") (uses := "beq_self_eq_true, cases, rfl, rw")
::::hint (anchor := "none")
::::

:::en
*true tested.* Now `true` stands in front: `true == b` is `b`.
:::

:::de
*true getestet.* Jetzt steht `true` vorne: `true == b` ist `b`.
:::
:::solution
```
cases b
rfl
rw [beq_self_eq_true]
```
:::
:::::

::::leanonly (proof := "(f : Bool → Bool) (μ : DiscreteMeasure Bool) (b : Bool) : (μ.map f) b = (bif f true == b then μ true else 0) + (bif f false == b then μ false else 0)") (new := "map_apply, sum_with") (lemma := "map_bool") (uses := "map_apply, sum_with, Fintype.sum_bool, rw")
:::en
*Where the mass goes.* A move `μ.map f` takes each point `a` with its mass `μ a` to `f a`. So the
mass at `b` is the sum of the masses of the points with `f a = b`:

`map_apply : (μ.map f) b = ∑ a with f a = b, μ a`.
:::

:::de
*Wohin die Masse geht.* Ein Zug `μ.map f` bringt jeden Punkt `a` mit seiner Masse `μ a` nach `f a`.
Die Masse bei `b` ist also die Summe der Massen der Punkte mit `f a = b`:

`map_apply : (μ.map f) b = ∑ a with f a = b, μ a`.
:::

:::proofen
`sum_with` writes the sum over the points with `f a = b` as a sum over all points, with a test.
Your result becomes the lemma `map_bool`.
:::

:::proofde
`sum_with` schreibt die Summe über die Punkte mit `f a = b` als Summe über alle Punkte, mit einem
Test. Dein Ergebnis wird das Lemma `map_bool`.
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

::::leanonly (proof := "(f : Bool → Bool) (μ : DiscreteMeasure Bool) : (μ.map f) true = (bif f true then μ true else 0) + (bif f false then μ false else 0)") (lemma := "map_true") (uses := "map_bool, beq_true, rw")
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
::::

:::::leanonly (proof := "(μ : DiscreteMeasure Bool) : (μ.map (fun _ => true)) true = ⟦μ true + μ false ‖ μ true, μ false, μ true + μ false, 0⟧") (uses := "map_true, Bool.cond_true, Bool.cond_false, rw, -rfl")
::::hint (anchor := "gap")
:::en
Which masses of `μ` come to `true`?
:::

:::de
Welche Massen von `μ` kommen bei `true` an?
:::
::::

:::en
*All to true.* The move *always `true`*, `fun _ => true`, sends both points to `true`.
:::

:::de
*Alles nach true.* Der Zug *immer `true`*, `fun _ => true`, schickt beide Punkte nach `true`.
:::

:::proofen
Your rule `map_true`, for the move *always `true`*.
:::

:::proofde
Deine Regel `map_true`, für den Zug *immer `true`*.
:::
:::solution
```
rw [map_true]
rw [Bool.cond_true, Bool.cond_true]
```
:::
:::::

:::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] : μ true + μ false = 1") (lemma := "mass_total") (new := "Prob.total, tsum_fintype") (uses := "Prob.total, tsum_fintype, Fintype.sum_bool, rw")
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
`1` of the goal this sum. `tsum_fintype` turns a sum over all points of a finite type into a finite
sum `∑`.
:::

:::proofde
`Prob.total μ : ∑' a, μ a = 1` ist eine Summe über alle Punkte, `∑'`; von rechts nach links gelesen
macht sie die `1` des Ziels zu dieser Summe. `tsum_fintype` macht eine Summe über alle Punkte eines
endlichen Typs zu einer endlichen Summe `∑`.
:::
:::solution
```
rw [← Prob.total μ, tsum_fintype, Fintype.sum_bool]
```
:::
:::::

:::::leanonly (proof := "(p : I) : coin p true + coin p false = ⟦1 ‖ 0, 1, p⟧") (lemma := "coin_total") (new := "exact") (uses := "mass_total, coin_total, exact")
::::hint (anchor := "item:exact")
:::en
`exact h`: closes a goal that is exactly `h`.
:::

:::de
`exact h`: schließt ein Ziel, das genau `h` ist.
:::
::::

:::en
*The whole mass of the coin.* What you proved for every distribution holds for the coin.
:::

:::de
*Die ganze Masse der Münze.* Was du für jede Verteilung bewiesen hast, gilt für die Münze.
:::

:::proofen
Your theorem `mass_total μ : μ true + μ false = 1` holds for every distribution `μ`: a rule with a
blank. What goes into the blank is written behind the rule, in brackets when it is more than a name.
The new tactic `exact h` closes a goal that is exactly `h`.
:::

:::proofde
Dein Satz `mass_total μ : μ true + μ false = 1` gilt für jede Verteilung `μ`: eine Regel mit einer
Leerstelle. Was in die Leerstelle kommt, schreibt man hinter die Regel, in Klammern, wenn es mehr
als ein Name ist. Die neue Taktik `exact h` schließt ein Ziel, das genau `h` ist.
:::
:::solution
```
exact mass_total (coin p)
```
:::
:::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] (b : Bool) : μ b ≤ 1") (lemma := "mass_le_one") (new := "le_self_add, add_comm") (uses := "mass_total, add_comm, le_self_add, coin_total, add_assoc, cases, exact, rw")
:::en
*At most one.* Each mass is a part of the whole mass, so at most one.
:::

:::de
*Höchstens eins.* Jede Masse ist ein Teil der ganzen Masse, also höchstens eins.
:::

:::proofen
The `1` is the whole mass, `mass_total μ`, and each mass is one of its summands:
`le_self_add : a ≤ a + c`. Where the summands stand the wrong way round, `add_comm : a + b = b + a`
turns the sum round.
:::

:::proofde
Die `1` ist die ganze Masse, `mass_total μ`, und jede Masse ist einer ihrer Summanden:
`le_self_add : a ≤ a + c`. Wo die Summanden falsch herum stehen, dreht `add_comm : a + b = b + a`
die Summe um.
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
::::

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
:::::

:::::circuit (height := "440") (inputs := "x") (gates := "not") (coins := "p") (target := "bool true:1-p false:p") (context := "Lean/Rules.lean") (proof := "(p : I) : ((coin p).map not) true = σ p") (play := "a=not; x>a.0; a>out") (uses := "map_true, Bool.not_true, Bool.not_false, Bool.cond_false, Bool.cond_true, zero_add, coin_false, add_zero, mul_zero, coin_true, coin_total, rw, -rfl")
:::hint (anchor := "none")
:::

:::hint (anchor := "none")
:::

:::en
*Boss: where does the mass go?* The coin `x` is thrown at the top; below, the output with the target:
`false` with mass $`p`, `true` with $`1 - p`. Put a `not` between them. Then look at `true`: its mass
came from `false`.
:::

:::de
*Endgegner: Wohin geht die Masse?* Oben wird die Münze `x` geworfen; unten der Ausgang mit dem Ziel: `false`
mit Masse $`p`, `true` mit $`1 - p`. Setz ein `nicht` dazwischen. Dann sieh dir `true` an: Seine
Masse kam von `false`.
:::

:::proofen
*Now the proof.* Everything it needs you know from *Bool* and this world.
:::

:::proofde
*Jetzt der Beweis.* Alles, was er braucht, kennst du aus *Bool* und dieser Welt.
:::
:::solution
```
rw [map_true]
rw [Bool.not_true, Bool.not_false]
rw [Bool.cond_false, Bool.cond_true, zero_add]
rw [coin_false]
```
:::
:::::
