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

::::circuit (height := "400") (inputs := "x") (gates := "") (coins := "p") (target := "bool true:p false:1-p") (context := "Lean/Rules.lean") (proof := "(p : I) : coin p true = p") (lemma := "coin_true") (play := "x>out") (uses := "-")
:::en
*The mass at true.* Now the coin. A coin shows `true` (heads) or `false` (tails); `coin p` is the coin
that shows `true` with probability $`p` and `false` with probability $`1 - p`. As a distribution on
`Bool` it has two masses: $`p` at `true` and $`1 - p` at `false`, together $`1`.

Here $`p` is a probability, a number between $`0` and $`1`: in Lean `p : I`, with $`I = [0, 1]` the
unit interval. Its counterpart $`1 - p` is written `σ p` (also in $`I`). A mass is a number in
$`[0, \infty]` (`ENNReal`); `↑p` is $`p` as a mass. With $`p = 1` the coin always shows `true`, with $`p = 0` always
`false`; with $`p = 1/2` it is a fair coin.

On the board: the coin `x` is thrown at the top. Wire it to the output, and the output has its two masses. In Lean: the mass of `coin p` at `true` is $`p`.
:::

:::de
*Die Masse bei true.* Jetzt die Münze. Eine Münze zeigt `true` (Kopf) oder `false` (Zahl); `coin p`
ist die Münze, die mit Wahrscheinlichkeit $`p` `true` zeigt und mit Wahrscheinlichkeit $`1 - p`
`false`. Als Verteilung auf `Bool` hat sie zwei Massen: $`p` bei `true` und $`1 - p` bei `false`,
zusammen $`1`.

Dabei ist $`p` eine Wahrscheinlichkeit, eine Zahl zwischen $`0` und $`1`: in Lean `p : I`, mit
$`I = [0, 1]` dem Einheitsintervall. Das Gegenstück $`1 - p` schreibt man `σ p` (auch in $`I`). Eine
Masse ist eine Zahl in $`[0, \infty]` (`ENNReal`); `↑p` ist $`p` als Masse. Mit $`p = 1` zeigt die Münze immer
`true`, mit $`p = 0` immer `false`; mit $`p = 1/2` ist sie fair.

Auf dem Spielfeld: Oben wird die Münze `x` geworfen. Verdrahte sie mit dem Ausgang, und der Ausgang hat ihre zwei Massen. In Lean: Die Masse von `coin p` bei `true` ist $`p`.
:::

:::proofen
`(coin p) true` is the mass of the coin at `true`. A distribution is, in Lean, its masses (its *weight* function):

```
structure DiscreteMeasure (α : Type) where
  weight : α → ENNReal
```

and the coin is defined by its two masses:

```
def coin (p : I) : DiscreteMeasure Bool where
  weight := fun
    | true => ↑p
    | false => ↑(σ p)
```

(`μ x` is `μ.weight x`.) So Lean computes the left side to `↑p`: `rfl`, as in *Circuits*. The
statement is the rule `coin_true`; once proved, it is in your inventory.

*Tip.* `rfl`.
:::

:::proofde
`(coin p) true` ist die Masse der Münze bei `true`. Eine Verteilung ist in Lean ihre Massen (ihre *Gewichtsfunktion*):

```
structure DiscreteMeasure (α : Type) where
  weight : α → ENNReal
```

und die Münze ist durch ihre zwei Massen definiert:

```
def coin (p : I) : DiscreteMeasure Bool where
  weight := fun
    | true => ↑p
    | false => ↑(σ p)
```

(`μ x` ist `μ.weight x`.) Also rechnet Lean die linke Seite zu `↑p` aus: `rfl`, wie in *Schaltungen*.
Die Aussage ist die Regel `coin_true`; bewiesen, ist sie in deinem Inventar.

*Tipp.* `rfl`.
:::
:::solution
```
rfl
```
:::
::::

:::::leanonly (proof := "(p : I) : coin p false = σ p") (lemma := "coin_false") (uses := "-")
::::hint (anchor := "statement")
:::en
`σ p := 1 - p`, computed in the unit interval: `σ p : I` (`unitInterval`), a probability again. As
a mass, `1 - p` would be `1 - ↑p : ℝ≥0∞`. The statement takes `σ p` and makes it a mass, `↑(σ p)`.
:::

:::de
`σ p := 1 - p`, gerechnet im Einheitsintervall: `σ p : I` (`unitInterval`), wieder eine
Wahrscheinlichkeit. Als Masse wäre `1 - p` dagegen `1 - ↑p : ℝ≥0∞`. Die Aussage nimmt `σ p` und
macht es zur Masse, `↑(σ p)`.
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

::::leanonly (proof := "(p : I) : 0 + coin p true = p") (new := "rw, zero_add") (uses := "zero_add, coin_true, add_zero, mul_zero, coin_false, coin_total")
:::en
*Zero plus.* Not every rule is a definition: `zero_add : 0 + a = a` is a rule of arithmetic, given
here (it is proved in Mathlib, not by `rfl`). A rule is used by rewriting with it.
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

::::leanonly (proof := "(f : Bool → Bool) (μ : DiscreteMeasure Bool) : (f <$> μ) true = (bif f true then μ true else 0) + (bif f false then μ false else 0)") (new := "map_apply") (lemma := "map_true") (uses := "map_apply, Fintype.sum_bool, beq_true")
:::en
*Where the mass goes.* A move `f <$> μ` takes each point `a` with its mass `μ a` to `f a`. So the
mass at `b` afterwards is the sum of the masses `μ a` of the points with `f a = b`. Lean defines it
so:

```
def map (f : α → β) (μ : DiscreteMeasure α) : DiscreteMeasure β where
  weight := fun b => ∑' a, (f⁻¹' {b}).indicator μ.weight a
```

(`f⁻¹' {b}` are the points `a` with `f a = b`; `indicator` is `μ a` there and `0` elsewhere; `∑'`
is a sum over possibly infinitely many points.) On a finite type, as `Bool`, it is a finite sum `∑`,
and the game writes the definition as the rule

`map_apply : (f <$> μ) b = ∑ a, (bif f a == b then μ a else 0)`.

From it you prove the rule of the gates, `map_true`: to `true` comes the mass at `true` when `f true`
is `true`, and the mass at `false` when `f false` is `true`.
:::

:::de
*Wohin die Masse geht.* Ein Zug `f <$> μ` bringt jeden Punkt `a` mit seiner Masse `μ a` nach `f a`.
Die Masse bei `b` danach ist also die Summe der Massen `μ a` der Punkte mit `f a = b`. Lean definiert
es so:

```
def map (f : α → β) (μ : DiscreteMeasure α) : DiscreteMeasure β where
  weight := fun b => ∑' a, (f⁻¹' {b}).indicator μ.weight a
```

(`f⁻¹' {b}` sind die Punkte `a` mit `f a = b`; `indicator` ist dort `μ a` und sonst `0`; `∑'` ist
eine Summe über möglicherweise unendlich viele Punkte.) Auf einem endlichen Typ, wie `Bool`, ist es
eine endliche Summe `∑`, und das Spiel schreibt die Definition als Regel

`map_apply : (f <$> μ) b = ∑ a, (bif f a == b then μ a else 0)`.

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

::::leanonly (proof := "(μ : DiscreteMeasure Bool) : ((fun _ => true) <$> μ) true = μ true + μ false") (uses := "map_true, Bool.cond_true, Bool.cond_false")
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
