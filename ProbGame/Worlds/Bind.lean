import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Coins that Wait" =>

%%%
htmlSplit := .never
%%%

:::en
Every board is given, and your task is always the same: choose what goes into the fields of the `bind`
gate, and drag it in. The `bind` gate looks at `x` (on top) and chooses a field, `T` or `F`.

A coin waits: it is thrown *after* the coin `x`, and **which** coin it is depends on what `x`
showed. The waiting coin `y` is a `bind` box with a coin in each field: `coin p`, `coin (σ p)`,
`pure true` or `pure false`, each with its small histogram. `y` becomes
`bif x then coin q else coin r`: first throw `x`, then, depending on what came, the one or the other
coin. In Lean: `do let x ← coin p; let y ← (bif x then coin q else coin r); …`, that is
`coin p >>= fun x => …`.

This world is one of two ways after *Building with Coins*; the other is *Counting*. They do not need
each other.
:::

:::de
Jedes Spielfeld ist gegeben, und deine Aufgabe ist immer dieselbe: Wähle, was in die Felder des
Bausteins `bind` kommt, und zieh es hinein. `bind` schaut auf `x` (oben) und wählt ein Feld, `T` oder
`F`.

Eine Münze wartet: Sie wird *nach* der Münze `x` geworfen, und **welche** Münze es ist, hängt davon
ab, was `x` zeigte. Die wartende Münze `y` ist ein `bind`-Kasten mit einer Münze in jedem Feld:
`coin p`, `coin (σ p)`, `pure true` oder `pure false`, jede mit ihrem kleinen Histogramm. `y` wird zu
`bif x then coin q else coin r`: erst `x` werfen, dann, je nachdem was kam, die eine oder die andere
Münze. In Lean: `do let x ← coin p; let y ← (bif x then coin q else coin r); …`, also

Diese Welt ist einer von zwei Wegen nach *Bauen mit Münzen*; der andere ist *Zählen*. Sie brauchen
einander nicht.
`coin p >>= fun x => …`.
:::

:::proofen
The statements are about the mass at `true`: the board shows the whole distribution, and your lemma
`bool_ext` says that the mass at `true` decides it. The new rule
`bind_true : (μ >>= f) true = μ true * f true true + μ false * f false true` goes both ways: through
`true` (the mass `μ true`, then the mass of `f true` at `true`) and through `false`.
:::

:::proofde
Die Aussagen handeln von der Masse bei `true`: Das Spielfeld zeigt die ganze Verteilung, und dein Lemma
`bool_ext` sagt, dass die Masse bei `true` sie festlegt. Die neue Regel
`bind_true : (μ >>= f) true = μ true * f true true + μ false * f false true` geht beide Wege: über
`true` (die Masse `μ true`, dann die Masse von `f true` bei `true`) und über `false`.
:::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) : (μ >>= fun _ => μ) true = μ true * μ true + μ false * μ true") (new := "bind_true")
:::en
*Two ways to true.* The mass of a draw at `true`: through `true` and through `false`.
:::

:::de
*Zwei Wege zu true.* Die Masse eines Ziehens bei `true`: über `true` und über `false`.
:::

:::proofen
`bind_true : (μ >>= f) true = μ true * f true true + μ false * f false true`: the mass at the first step times the mass at `true` of what follows, for both values of the first step. That is the mass of a draw, by the definition of `>>=`:

```
(μ >>= f) b = ∑' a, μ a * (f a) b
```

on `Bool` a sum of two summands.

*Tip.* `rw [bind_true]`.
:::

:::proofde
`bind_true : (μ >>= f) true = μ true * f true true + μ false * f false true`: die Masse im ersten Schritt mal die Masse bei `true` dessen, was folgt, für beide Werte des ersten Schritts. Das ist die Masse eines Ziehens, nach der Definition von `>>=`:

```
(μ >>= f) b = ∑' a, μ a * (f a) b
```

auf `Bool` eine Summe aus zwei Summanden.

*Tipp.* `rw [bind_true]`.
:::
:::solution
```
rw [bind_true]
```
:::
::::

::::circuit (inputs := "x y z") (gates := "") (coins := "p ?|? ?|?") (target := "bool true:3p-3p^2+p^3 false:(1-p)^3") (start := "x>y.0; y>z.0; z>out") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← (bif x then pure true else coin p); let z ← (bif y then pure true else coin p); pure z) true = (↑p + ↑(σ p) * (↑p + ↑(σ p) * ↑p) : ENNReal)") (play := "y.T=1; y.F=p; z.T=1; z.F=p")
:::en
*Boss: three tries.* Throw until `true` comes, at most three times. `y` waits for `x`, and `z` waits
for `y`. `false` only when all three tries fail: $`(1 - p)^3`.
:::

:::de
*Boss: drei Versuche.* Wirf, bis `true` kommt, höchstens dreimal. `y` wartet auf `x`, und `z` wartet auf
`y`. `false` nur, wenn alle drei Versuche scheitern: $`(1 - p)^3`.
:::

:::proofen
`bind_true` twice. After the first, the way through `false` is a bind again, inside the computation,
where `rw` would have to pick the right place: give the rule to `norm_num` instead,
`norm_num [bind_true]`, and it uses it wherever it fits. (The way through `true` starts with
`pure true`; `pure_bind` throws it away, and `norm_num` knows that rule by itself.)

*Tip.* `rw [bind_true]`, then `norm_num [bind_true]`.
:::

:::proofde
Zweimal `bind_true`. Nach dem ersten ist der Weg über `false` wieder ein bind, mitten in der Rechnung,
wo `rw` die richtige Stelle treffen müsste: Gib die Regel stattdessen `norm_num`,
`norm_num [bind_true]`, und es benutzt sie, wo sie passt. (Der Weg über `true` beginnt mit
`pure true`; `pure_bind` wirft es weg, und diese Regel kennt `norm_num` von selbst.)

*Tipp.* `rw [bind_true]`, dann `norm_num [bind_true]`.
:::
:::solution
```
rw [bind_true]
norm_num [bind_true]
```
:::
::::
