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
Before the first coin: how Lean writes a distribution, and the rules that *One Coin* needs, each in a
level of its own. Most of them hold by definition, and the proof is `rfl`.

A distribution on `Bool` is, in Lean, `μ : DiscreteMeasure Bool`: it gives each of the two points its
*mass*, `μ true` and `μ false`, the heights of its two bars. The coin with probability $`p` is
`coin p`. A move is written `f <$> μ`: the map `f` applied to the distribution `μ`, its image measure.
:::

:::de
Vor der ersten Münze: wie Lean eine Verteilung schreibt, und die Regeln, die *Eine Münze* braucht,
jede in einem eigenen Level. Die meisten gelten nach Definition, und der Beweis ist `rfl`.

Eine Verteilung auf `Bool` ist in Lean `μ : DiscreteMeasure Bool`: Sie gibt jedem der beiden Punkte
seine *Masse*, `μ true` und `μ false`, die Höhen ihrer beiden Säulen. Die Münze mit Wahrscheinlichkeit
$`p` ist `coin p`. Ein Zug wird `f <$> μ` geschrieben: die Abbildung `f`, angewandt auf die Verteilung
`μ`, ihr Bildmaß.
:::

::::leanonly (proof := "(a b : ENNReal) : (bif true then a else b) = a") (lemma := "Bool.cond_true") (uses := "-")
:::en
*bif with true.* `bif c then a else b` is `a` when `c` is `true`, and `b` when it is `false`: an
if-then-else for a `Bool`. *One Coin* needs it to say where the mass of a move goes.
:::

:::de
*bif mit true.* `bif c then a else b` ist `a`, wenn `c` gleich `true` ist, und `b`, wenn es `false`
ist: ein Wenn-dann-sonst für ein `Bool`. *Eine Münze* braucht es, um zu sagen, wohin die Masse eines
Zuges geht.
:::

:::proofen
`a b : ENNReal` are two masses. `bif` is defined by the two cases of `c`; here `c` is `true`.

*Tip.* `rfl`.
:::

:::proofde
`a b : ENNReal` sind zwei Massen. `bif` ist durch die zwei Fälle von `c` definiert; hier ist `c`
gleich `true`.

*Tipp.* `rfl`.
:::
:::solution
```
rfl
```
:::
::::

::::leanonly (proof := "(a b : ENNReal) : (bif false then a else b) = b") (lemma := "Bool.cond_false") (uses := "-")
:::en
*bif with false.* The other case: the second.
:::

:::de
*bif mit false.* Der andere Fall: das Zweite.
:::

:::proofen
*Tip.* `rfl`.
:::

:::proofde
*Tipp.* `rfl`.
:::
:::solution
```
rfl
```
:::
::::

::::leanonly (proof := "(p : I) : coin p true = p") (lemma := "coin_true") (uses := "-")
:::en
*The mass at true.* Now the coin. A coin shows `true` (heads) or `false` (tails); `coin p` is the coin
that shows `true` with probability $`p` and `false` with probability $`1 - p`. As a distribution on
`Bool` it has two masses: $`p` at `true` and $`1 - p` at `false`, together $`1`.

Here $`p` is a probability, a number between $`0` and $`1`: in Lean `p : I`, with $`I = [0, 1]` the
unit interval. Its counterpart $`1 - p` is written `σ p` (also in $`I`). A mass is a number in
$`[0, \infty]` (`ENNReal`); `↑p` is $`p` as a mass. With $`p = 1` the coin always shows `true`, with $`p = 0` always
`false`; with $`p = 1/2` it is a fair coin.

This level: the mass of `coin p` at `true` is $`p`.
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

Dieses Level: Die Masse von `coin p` bei `true` ist $`p`.
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

::::leanonly (proof := "(p : I) : coin p false = σ p") (lemma := "coin_false") (uses := "-")
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
::::

::::leanonly (proof := "(p : I) : 0 + coin p true = p") (new := "rw, zero_add") (uses := "zero_add, coin_true, add_zero, mul_zero, coin_false")
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

::::leanonly (proof := "(μ : DiscreteMeasure Bool) : ((fun _ => true) <$> μ) true = μ true + μ false") (new := "map_true") (uses := "map_true, Bool.cond_true, Bool.cond_false")
:::en
*Where the mass goes.* The move *always `true`*, `fun _ => true`, sends both points to `true`; so all
the mass of `μ` comes to `true`. This is the rule of the gates, given (it is proved from the definition
of `<$>`, but not by `rfl`):

`map_true : (f <$> μ) true = (bif f true then μ true else 0) + (bif f false then μ false else 0)`.

To `true` comes the mass at `true` when `f true` is `true`, and the mass at `false` when `f false` is
`true`. That is what the definition of a move says on `Bool`:

```
def map (f : α → β) (μ : DiscreteMeasure α) : DiscreteMeasure β where
  weight := fun b => ∑' a, (f⁻¹' {b}).indicator μ.weight a
```

The mass at `b` is the sum of the masses `μ a` over the points `a` with `f a = b` (the preimage
`f⁻¹' {b}`; `indicator` is zero outside it). On `Bool` the sum has two summands.
:::

:::de
*Wohin die Masse geht.* Der Zug *immer `true`*, `fun _ => true`, schickt beide Punkte nach `true`;
also kommt die ganze Masse von `μ` nach `true`. Das ist die Regel der Bausteine, gegeben (sie folgt aus
der Definition von `<$>`, aber nicht mit `rfl`):

`map_true : (f <$> μ) true = (bif f true then μ true else 0) + (bif f false then μ false else 0)`.

Nach `true` kommt die Masse bei `true`, wenn `f true` gleich `true` ist, und die Masse bei `false`,
wenn `f false` gleich `true` ist. Das sagt die Definition eines Zuges auf `Bool`:

```
def map (f : α → β) (μ : DiscreteMeasure α) : DiscreteMeasure β where
  weight := fun b => ∑' a, (f⁻¹' {b}).indicator μ.weight a
```

Die Masse bei `b` ist die Summe der Massen `μ a` über die Punkte `a` mit `f a = b` (das Urbild
`f⁻¹' {b}`; `indicator` ist außerhalb davon null). Auf `Bool` hat die Summe zwei Summanden.
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
