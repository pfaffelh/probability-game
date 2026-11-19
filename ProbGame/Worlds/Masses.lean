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

:::::circuit (height := "400") (inputs := "x") (gates := "") (coins := "p") (target := "bool true:p false:1-p") (context := "Lean/Rules.lean") (proof := "(p : I) : coin p true = p") (lemma := "coin_true") (play := "x>out") (uses := "-")
:::en
*The mass at true.* A coin shows `true` (heads) or `false` (tails); `coin p` is the coin
that shows `true` with probability $`p` and `false` with probability $`1 - p`. As a distribution on
`Bool` it has two masses: $`p` at `true` and $`1 - p` at `false`.
:::

:::de
*Die Masse bei true.* Eine Münze zeigt `true` (Kopf) oder `false` (Zahl); `coin p`
ist die Münze, die mit Wahrscheinlichkeit $`p` `true` zeigt und mit Wahrscheinlichkeit $`1 - p`
`false`. Als Verteilung auf `Bool` hat sie zwei Massen: $`p` bei `true` und $`1 - p` bei `false`.
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
`I`. The arrow `↑` makes a number of `I` a mass in `ℝ≥0∞`. (`μ x` is `μ.weight x`.) So Lean computes the left side to `↑p`: `rfl`, as in *Circuits*. The
statement is the rule `coin_true`; once proved, it is in your inventory.

*Tip.* `rfl`.
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
`μ.weight x`.) Also rechnet Lean die linke Seite zu `↑p` aus: `rfl`, wie in *Schaltungen*.
Die Aussage ist die Regel `coin_true`; bewiesen, ist sie in deinem Inventar.

*Tipp.* `rfl`.
:::
:::solution
```
rfl
```
:::
:::::

:::::leanonly (proof := "(p : I) : coin p false = σ p") (lemma := "coin_false") (uses := "-")
::::hint (anchor := "statement")
:::en
We have `p : I`, and `I` is a subtype of `ℝ`: the real numbers `x` with `0 ≤ x ≤ 1`. As a mass, `p`
becomes `↑p : ℝ≥0∞`. We have `1 - ↑p : ℝ≥0∞`, but also `σ p := 1 - p : I`. In other words, `σ p` and
`1 - ↑p` are the same number, but `σ p` has type `I` and `1 - ↑p` has type `ℝ≥0∞`. The statement
makes `σ p` a mass: `↑(σ p)`.
:::

:::de
Wir haben `p : I`, und `I` ist ein Subtyp von `ℝ`: die reellen Zahlen `x` mit `0 ≤ x ≤ 1`. Als Masse
wird `p` zu `↑p : ℝ≥0∞`. Es gibt `1 - ↑p : ℝ≥0∞`, aber auch `σ p := 1 - p : I`. Mit anderen Worten:
`σ p` und `1 - ↑p` sind dieselbe Zahl, aber `σ p` hat den Typ `I` und `1 - ↑p` den Typ `ℝ≥0∞`. Die
Aussage macht `σ p` zur Masse: `↑(σ p)`.
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

*Tip.* `rfl`.
:::

:::proofde
`σ p` ist $`1 - p`, wieder in $`I`, und `↑(σ p)` ist das als Masse. Wieder nach der Definition von `coin` (die Zeile `| false => ↑(σ p)`).

*Tipp.* `rfl`.
:::
:::solution
```
rfl
```
:::
:::::

::::leanonly (proof := "(p : I) : 0 + coin p true = p") (new := "zero_add") (uses := "zero_add, coin_true, add_zero, mul_zero, coin_false, coin_total")
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
A rule `h : a = b` is used with `rw [h]`: it rewrites `a` into `b` in the goal (`rw [← h]` the other
way round), several at once with `rw [h, k]`. When the goal then reads `x = x`, it is closed.
`rw [zero_add]` takes the `0 + ` away; then your rule `coin_true`.

*Tip.* `rw [zero_add]`, then `rw [coin_true]` (or both at once: `rw [zero_add, coin_true]`).
:::

:::proofde
Eine Regel `h : a = b` benutzt man mit `rw [h]`: Sie schreibt `a` im Ziel zu `b` um (`rw [← h]`
andersherum), mehrere auf einmal mit `rw [h, k]`. Lautet das Ziel danach `x = x`, ist es geschlossen.
`rw [zero_add]` nimmt das `0 + ` weg; dann deine Regel `coin_true`.

*Tipp.* `rw [zero_add]`, dann `rw [coin_true]` (oder beides auf einmal: `rw [zero_add, coin_true]`).
:::
:::solution
```
rw [zero_add]
rw [coin_true]
```
:::
::::

::::leanonly (proof := "(x y : ENNReal) : ∑ a, (bif a then x else y) = x + y") (new := "Fintype.sum_bool") (uses := "Fintype.sum_bool, Bool.cond_true, Bool.cond_false")
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
Here `g a` is `bif a then x else y`. After `rw [Fintype.sum_bool]` you have `bif true …` and `bif false …`.

*Tip.* `rw [Fintype.sum_bool, Bool.cond_true, Bool.cond_false]`.
:::

:::proofde
Hier ist `g a` gleich `bif a then x else y`. Nach `rw [Fintype.sum_bool]` stehen da `bif true …` und
`bif false …`.

*Tipp.* `rw [Fintype.sum_bool, Bool.cond_true, Bool.cond_false]`.
:::
:::solution
```
rw [Fintype.sum_bool, Bool.cond_true, Bool.cond_false]
```
:::
::::

::::leanonly (proof := "(c : Bool) : (c == true) = c") (lemma := "beq_true") (uses := "-")
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
Two cases, as in *Circuits*: `c` is `true` or `false`, and in each Lean computes both sides.

*Tip.* `cases c <;> rfl`.
:::

:::proofde
Zwei Fälle, wie in *Schaltungen*: `c` ist `true` oder `false`, und in jedem rechnet Lean beide Seiten
aus.

*Tipp.* `cases c <;> rfl`.
:::
:::solution
```
cases c <;> rfl
```
:::
::::

::::leanonly (proof := "(f : Bool → Bool) (μ : DiscreteMeasure Bool) : (μ.map f) true = (bif f true then μ true else 0) + (bif f false then μ false else 0)") (new := "map_apply") (lemma := "map_true") (uses := "map_apply, Fintype.sum_bool, beq_true")
:::en
*Where the mass goes.* A move `μ.map f` takes each point `a` with its mass `μ a` to `f a`. So the
mass at `b` afterwards is the sum of the masses `μ a` of the points with `f a = b`. Lean defines it
so:

```
def map (f : α → β) (μ : DiscreteMeasure α) : DiscreteMeasure β where
  weight := fun b => ∑' a, (f⁻¹' {b}).indicator μ.weight a
```

(`f⁻¹' {b}` are the points `a` with `f a = b`; `indicator` is `μ a` there and `0` elsewhere; `∑'`
is a sum over possibly infinitely many points.) On a finite type, as `Bool`, it is a finite sum `∑`,
and the game writes the definition as the rule

`map_apply : (μ.map f) b = ∑ a, (bif f a == b then μ a else 0)`.

From it you prove the rule of the gates, `map_true`: to `true` comes the mass at `true` when `f true`
is `true`, and the mass at `false` when `f false` is `true`.
:::

:::de
*Wohin die Masse geht.* Ein Zug `μ.map f` bringt jeden Punkt `a` mit seiner Masse `μ a` nach `f a`.
Die Masse bei `b` danach ist also die Summe der Massen `μ a` der Punkte mit `f a = b`. Lean definiert
es so:

```
def map (f : α → β) (μ : DiscreteMeasure α) : DiscreteMeasure β where
  weight := fun b => ∑' a, (f⁻¹' {b}).indicator μ.weight a
```

(`f⁻¹' {b}` sind die Punkte `a` mit `f a = b`; `indicator` ist dort `μ a` und sonst `0`; `∑'` ist
eine Summe über möglicherweise unendlich viele Punkte.) Auf einem endlichen Typ, wie `Bool`, ist es
eine endliche Summe `∑`, und das Spiel schreibt die Definition als Regel

`map_apply : (μ.map f) b = ∑ a, (bif f a == b then μ a else 0)`.

Daraus beweist du die Regel der Bausteine, `map_true`: Nach `true` kommt die Masse bei `true`, wenn
`f true` gleich `true` ist, und die Masse bei `false`, wenn `f false` gleich `true` ist.
:::

:::proofen
`rw [map_apply]` writes the mass as a sum, `rw [Fintype.sum_bool]` as its two summands. Then the tests
`f true == true` and `f false == true`: your rule `beq_true`, twice.

*Tip.* `rw [map_apply, Fintype.sum_bool]`, then `rw [beq_true, beq_true]`.
:::

:::proofde
`rw [map_apply]` schreibt die Masse als Summe, `rw [Fintype.sum_bool]` als ihre zwei Summanden. Dann die
Tests `f true == true` und `f false == true`: deine Regel `beq_true`, zweimal.

*Tipp.* `rw [map_apply, Fintype.sum_bool]`, dann `rw [beq_true, beq_true]`.
:::
:::solution
```
rw [map_apply, Fintype.sum_bool]
rw [beq_true, beq_true]
```
:::
::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) : (μ.map (fun _ => true)) true = μ true + μ false") (uses := "map_true, Bool.cond_true, Bool.cond_false")
:::en
*All to true.* The move *always `true`*, `fun _ => true`, sends both points to `true`; so all the
mass of `μ` comes to `true`. Your rule `map_true` says so.
:::

:::de
*Alles nach true.* Der Zug *immer `true`*, `fun _ => true`, schickt beide Punkte nach `true`; also
kommt die ganze Masse von `μ` nach `true`. Deine Regel `map_true` sagt das.
:::

:::proofen
After `rw [map_true]` both conditions read `true`: your rule `Bool.cond_true`, twice.

*Tip.* `rw [map_true]`, then `rw [Bool.cond_true, Bool.cond_true]`.
:::

:::proofde
Nach `rw [map_true]` lauten beide Bedingungen `true`: deine Regel `Bool.cond_true`, zweimal.

*Tipp.* `rw [map_true]`, dann `rw [Bool.cond_true, Bool.cond_true]`.
:::
:::solution
```
rw [map_true]
rw [Bool.cond_true, Bool.cond_true]
```
:::
::::

:::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] : μ true + μ false = 1") (lemma := "mass_total") (new := "Prob.total, tsum_fintype") (uses := "Prob.total, tsum_fintype, Fintype.sum_bool")
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

:::proofen
`Prob.total μ : ∑' a, μ a = 1` is a sum over all points, `∑'`. Read from right to left,
`rw [← Prob.total μ]` makes the `1` of the goal this sum. `tsum_fintype` turns a sum over all points
of a finite type into a finite sum `∑`, and `Fintype.sum_bool` into its two summands.

*Tip.* `rw [← Prob.total μ, tsum_fintype, Fintype.sum_bool]` (type `\l` for `←`, or tap ←).
:::

:::proofde
`Prob.total μ : ∑' a, μ a = 1` ist eine Summe über alle Punkte, `∑'`. Von rechts nach links gelesen
macht `rw [← Prob.total μ]` die `1` des Ziels zu dieser Summe. `tsum_fintype` macht eine Summe über
alle Punkte eines endlichen Typs zu einer endlichen Summe `∑`, und `Fintype.sum_bool` zu ihren zwei
Summanden.

*Tipp.* `rw [← Prob.total μ, tsum_fintype, Fintype.sum_bool]` (`\l` tippen für `←`, oder ← antippen).
:::
:::solution
```
rw [← Prob.total μ, tsum_fintype, Fintype.sum_bool]
```
:::
:::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] (b : Bool) : μ b ≤ 1") (lemma := "mass_le_one") (new := "exact, le_self_add, le_add_self") (uses := "mass_total, le_add_self, le_self_add, coin_total")
:::en
*At most one.* Each mass is a part of the whole mass, so at most one.
:::

:::de
*Höchstens eins.* Jede Masse ist ein Teil der ganzen Masse, also höchstens eins.
:::

:::proofen
`rw [← mass_total μ]` makes the `1` the whole mass; `cases b` gives the two points. Then the goal is
exactly a rule: `le_self_add : a ≤ a + c` or `le_add_self : a ≤ c + a`. `exact h` closes a goal that
is exactly `h`.

*Tip.* `rw [← mass_total μ]`, `cases b`, `exact le_add_self`, `exact le_self_add`.
:::

:::proofde
`rw [← mass_total μ]` macht die `1` zur ganzen Masse; `cases b` gibt die zwei Punkte. Dann ist das
Ziel genau eine Regel: `le_self_add : a ≤ a + c` oder `le_add_self : a ≤ c + a`. `exact h` schließt
ein Ziel, das genau `h` ist.

*Tipp.* `rw [← mass_total μ]`, `cases b`, `exact le_add_self`, `exact le_self_add`.
:::
:::solution
```
rw [← mass_total μ]
cases b
exact le_add_self
exact le_self_add
```
:::
::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] (b : Bool) : μ b ≠ ⊤") (lemma := "mass_ne_top") (new := "apply, ne_top_of_le_ne_top, ENNReal.one_ne_top") (uses := "ne_top_of_le_ne_top, ENNReal.one_ne_top, mass_le_one")
:::en
*Finite.* Masses are numbers in $`[0, \infty]`; a mass of a distribution is finite, `≠ ⊤`
(`⊤` is $`\infty`): it is at most one, and one is finite.
:::

:::de
*Endlich.* Massen sind Zahlen in $`[0, \infty]`; eine Masse einer Verteilung ist endlich, `≠ ⊤`
(`⊤` ist $`\infty`): Sie ist höchstens eins, und eins ist endlich.
:::

:::proofen
`ne_top_of_le_ne_top : b ≠ ⊤ → a ≤ b → a ≠ ⊤`. `apply h` works backwards: the goal is the conclusion
of `h`, and what `h` still needs becomes the new goal. With `b = 1` and `ENNReal.one_ne_top : 1 ≠ ⊤`
given, what is left is `μ b ≤ 1`: your theorem `mass_le_one`.

*Tip.* `apply ne_top_of_le_ne_top ENNReal.one_ne_top`, then `exact mass_le_one μ b`.
:::

:::proofde
`ne_top_of_le_ne_top : b ≠ ⊤ → a ≤ b → a ≠ ⊤`. `apply h` arbeitet rückwärts: Das Ziel ist die
Folgerung von `h`, und was `h` noch braucht, wird das neue Ziel. Mit `b = 1` und
`ENNReal.one_ne_top : 1 ≠ ⊤` gegeben, bleibt `μ b ≤ 1`: dein Satz `mass_le_one`.

*Tipp.* `apply ne_top_of_le_ne_top ENNReal.one_ne_top`, dann `exact mass_le_one μ b`.
:::
:::solution
```
apply ne_top_of_le_ne_top ENNReal.one_ne_top
exact mass_le_one μ b
```
:::
::::

:::::circuit (height := "440") (inputs := "x") (gates := "not") (coins := "p") (target := "bool true:1-p false:p") (context := "Lean/Rules.lean") (proof := "(p : I) : ((coin p).map not) true = ⟦σ p ‖ p, σ p, 1, 0⟧") (play := "a=not; x>a.0; a>out") (uses := "map_true, Bool.not_true, Bool.not_false, Bool.cond_false, Bool.cond_true, zero_add, coin_false, add_zero, mul_zero, coin_true, coin_total")
:::hint (anchor := "none")
:::

:::hint (anchor := "none")
:::

:::en
*Where does the mass go?* The coin `x` is thrown at the top; below, the output with the target:
`false` with mass $`p`, `true` with $`1 - p`. Put a `not` between them. Then look at `true`: its mass
came from `false`.
:::

:::de
*Wohin geht die Masse?* Oben wird die Münze `x` geworfen; unten der Ausgang mit dem Ziel: `false`
mit Masse $`p`, `true` mit $`1 - p`. Setz ein `nicht` dazwischen. Dann sieh dir `true` an: Seine
Masse kam von `false`.
:::

:::proofen
*Now the proof.* Everything it needs you know from *Circuits* and this world: `coin p` and its masses, `μ.map f`, and
the rules. First the rule of the gates, `map_true`; then computing, one rule after another:
`Bool.not_true`, `Bool.not_false`, `Bool.cond_false`, `Bool.cond_true`, `zero_add` and `coin_false`.

*Tip.* `rw [map_true]`, `rw [Bool.not_true, Bool.not_false]`,
`rw [Bool.cond_false, Bool.cond_true, zero_add]`, `rw [coin_false]` (type it, or tap the inventory,
and press *Run*).
:::

:::proofde
*Jetzt der Beweis.* Alles, was er braucht, kennst du aus *Schaltungen* und dieser Welt: `coin p` und seine Massen,
`μ.map f` und die Regeln. Zuerst die Regel der Bausteine, `map_true`; dann Rechnen, eine Regel nach der
anderen: `Bool.not_true`, `Bool.not_false`, `Bool.cond_false`, `Bool.cond_true`, `zero_add` und
`coin_false`.

*Tipp.* `rw [map_true]`, `rw [Bool.not_true, Bool.not_false]`,
`rw [Bool.cond_false, Bool.cond_true, zero_add]`, `rw [coin_false]`.
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
