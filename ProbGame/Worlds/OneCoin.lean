import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "One Coin" =>

%%%
htmlSplit := .never
%%%

:::en
A coin shows `true` with probability $`p` and `false` with probability $`1 - p`, for any $`p`, as in
Lean, where a coin is a random `Bool`. Its distribution gives each outcome its *mass*, here $`1 - p`
and $`p`; the masses add up to $`1`. A distribution is the same as a probability measure.

The board is played from top to bottom, as in *Bool*: at the top the coin `x ← coin p` is thrown,
below it the gates, at the bottom the output box with the target. A gate applies a map $`f` to the
outcome: the mass of each outcome goes to its image, and where several outcomes have the same image,
their masses add up. What comes out is the distribution of $`f(X)`, the *image measure*
$`P \circ f^{-1}`: $`P(f(X) = b) = P(X \in f^{-1}(\{b\}))`. The output box shows the target and your
output, as masses and as a small histogram (the target dashed), drawn for an example $`p`; the slider
in the bar at the bottom changes it.
:::

:::de
Eine Münze zeigt `true` mit Wahrscheinlichkeit $`p` und `false` mit Wahrscheinlichkeit $`1 - p`, für
ein beliebiges $`p`, wie in Lean, wo eine Münze ein zufälliges `Bool` ist. Ihre Verteilung gibt jedem
Ergebnis seine *Masse*, hier $`1 - p` und $`p`; die Massen ergeben zusammen $`1`. Eine Verteilung ist
dasselbe wie ein Wahrscheinlichkeitsmaß.

Das Spielfeld wird von oben nach unten gespielt, wie in *Bool*: Oben wird die Münze
`x ← coin p` geworfen, darunter die Bausteine, unten der Ausgabekasten mit dem Ziel. Ein Baustein wendet
eine Abbildung $`f` auf das Ergebnis an: Die Masse jedes Ergebnisses geht zu seinem Bild, und wo mehrere
Ergebnisse dasselbe Bild haben, addieren sich ihre Massen. Was herauskommt, ist die Verteilung von
$`f(X)`, das *Bildmaß* $`P \circ f^{-1}`: $`P(f(X) = b) = P(X \in f^{-1}(\{b\}))`. Der Ausgabekasten
zeigt Ziel und Ausgang, als Massen und als kleines Histogramm (das Ziel gestrichelt), gezeichnet für ein
Beispiel-$`p`; der Schieberegler in der Leiste unten ändert es.
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
`(coin p) true` is the mass of the coin at `true`. The coin is defined by its two masses:

```
def coin (p : I) : DiscreteMeasure Bool where
  weight := fun
    | true => ↑p
    | false => ↑(σ p)
```

`I` is the unit interval $`[0, 1]`, where the probability `p` lies; `σ p` is $`1 - p`, again in
`I`. The arrow `↑` makes a number of `I` a mass in `ℝ≥0∞`. So the statement holds by definition. The
statement is the rule `coin_true`; once proved, it is in your inventory.
:::

:::proofde
`(coin p) true` ist die Masse der Münze bei `true`. Die Münze ist durch ihre zwei Massen definiert:

```
def coin (p : I) : DiscreteMeasure Bool where
  weight := fun
    | true => ↑p
    | false => ↑(σ p)
```

`I` ist das Einheitsintervall $`[0, 1]`, in dem die Wahrscheinlichkeit `p` liegt; `σ p` ist $`1 - p`,
wieder in `I`. Der Pfeil `↑` macht aus einer Zahl aus `I` eine Masse in `ℝ≥0∞`. Also gilt die Aussage nach Definition.
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

::::leanonly (proof := "(p : I) : coin p true + coin p false = ⟦1 ‖ 0, 1, p⟧") (lemma := "coin_total") (uses := "coin_true, coin_false, add_symm_eq_one, coin_total, rw")
:::en
*The coin is whole.* $`p + (1 - p) = 1`: the two masses of the coin add up to one.
:::

:::de
*Die Münze ist ganz.* $`p + (1 - p) = 1`: Die beiden Massen der Münze ergeben zusammen eins.
:::

:::proofen
The rule `add_symm_eq_one p : ↑p + ↑(σ p) = 1` from *ENNReal*. First write the masses of the coin as
`↑p` and `↑(σ p)`. What you prove is unlocked as `coin_total`.
:::

:::proofde
Die Regel `add_symm_eq_one p : ↑p + ↑(σ p) = 1` aus *ENNReal*. Schreib zuerst die Massen der Münze als
`↑p` und `↑(σ p)`. Was du beweist, wird als `coin_total`
freigeschaltet.
:::
:::solution
```
rw [coin_true, coin_false, add_symm_eq_one]
```
:::
:::solution
```
rw [coin_true, coin_false]
rw [add_symm_eq_one p]
```
:::
:::solution
```
rw [← add_symm_eq_one p, coin_true, coin_false]
```
:::
::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] (p : I) (h : μ true = p) : μ = coin ⟦p ‖ p, σ p⟧") (lemma := "eq_coin") (uses := "bool_ext, coin_true, coin_false, coin_total, apply, exact, rfl, rw")
:::hint (anchor := "none")
:::

:::en
*Every distribution is a coin.* A distribution on `Bool` with mass `p` at `true` is the coin `p`.
So the coins are all there is on `Bool`.
:::

:::de
*Jede Verteilung ist eine Münze.* Eine Verteilung auf `Bool` mit Masse `p` bei `true` ist die Münze
`p`. Mehr als Münzen gibt es auf `Bool` also nicht.
:::

:::proofen
Your lemma `bool_ext` says: `μ = ν`, if `μ true = ν true`. The goal here is `μ = coin p`, an
equation of two distributions on `Bool`: `apply` (from *ENNReal*) uses the lemma from its end.
:::

:::proofde
Dein Lemma `bool_ext` sagt: `μ = ν`, wenn `μ true = ν true`. Das Ziel hier ist `μ = coin p`, eine
Gleichung zweier Verteilungen auf `Bool`: `apply` (aus *ENNReal*) benutzt das Lemma von seinem Ende
her.
:::
:::solution
```
apply bool_ext
rw [coin_true, h]
```
:::
:::solution
```
apply bool_ext
rw [coin_true]
exact h
```
:::
:::solution
```
apply bool_ext
rw [h]
rfl
```
:::
:::solution
```
exact bool_ext μ (coin p) h
```
:::
::::

::::leanonly (proof := ": coin 1 = ⟦pure true ‖ pure true, pure false⟧") (lemma := "coin_one") (uses := "bool_ext, coin_true, pure_true, Bool.cond_true, mass_one, coin_false, coin_total, Bool.cond_false, apply, rw")
:::en
*A sure coin.* The coin with probability one shows `true` for sure.
:::

:::de
*Eine sichere Münze.* Die Münze mit Wahrscheinlichkeit eins zeigt sicher `true`.
:::

:::proofen
Compare the masses at `true` (`bool_ext`); `mass_one : ↑(1 : I) = 1` is from *ENNReal*. What you prove is unlocked as `coin_one`.
:::

:::proofde
Vergleiche die Massen bei `true` (`bool_ext`); `mass_one : ↑(1 : I) = 1` ist aus *ENNReal*. Was du beweist, wird als `coin_one` freigeschaltet.
:::
:::solution
```
apply bool_ext
rw [coin_true, pure_true, Bool.cond_true, mass_one]
```
:::
:::solution
```
apply bool_ext
rw [coin_true, mass_one, pure_true, Bool.cond_true]
```
:::
::::

::::circuit (height := "540") (inputs := "x") (gates := "not, alwaysT") (coins := "p") (target := "pure false") (context := "Lean/Rules.lean") (proof := "(p : I) : ((coin p).map (fun _ => true)).map not = pure false") (play := "a=alwaysT; b=not; x>a.0; a>b.0; b>out") (uses := "bool_ext, map_not_true, map_bool, Bool.true_beq, Bool.cond_false, zero_add, pure_true, Bool.cond_true, add_zero, mul_zero, apply, rw")
:::hint (anchor := "none")
:::

:::en
*Surely `false`, but there is no “always `false`”.* Two gates one after the other: the image measure of
the image measure is the image measure of the composition, $`(P \circ f^{-1}) \circ g^{-1} = P \circ (g \circ f)^{-1}`.
:::

:::de
*Sicher `false`, aber es gibt kein „immer `false`“.* Zwei Bausteine nacheinander: Das Bildmaß des Bildmaßes ist
das Bildmaß der Verkettung, $`(P \circ f^{-1}) \circ g^{-1} = P \circ (g \circ f)^{-1}`.
:::

:::proofen
Compare the masses at `true` (`bool_ext`). The last gate is `not`: your boss `map_not_true` of
*DiscreteMeasure*. Before it, *always `true`* sends no mass to `false`: `map_bool`.
:::

:::proofde
Vergleiche die Massen bei `true` (`bool_ext`). Der letzte Baustein ist `not`: dein Endgegner
`map_not_true` aus *DiscreteMeasure*. Davor schickt *immer `true`* keine Masse nach `false`: `map_bool`.
:::
:::solution
```
apply bool_ext
rw [map_not_true, map_bool, Bool.true_beq, Bool.cond_false, Bool.cond_false, zero_add, pure_true, Bool.cond_false]
```
:::
:::solution
```
apply bool_ext
rw [map_not_true, pure_true, Bool.cond_false]
rw [map_bool, Bool.true_beq, Bool.cond_false, Bool.cond_false, zero_add]
```
:::
::::

:::::circuit (height := "440") (inputs := "x") (gates := "not") (coins := "p") (target := "bool true:1-p false:p") (context := "Lean/Rules.lean") (proof := "(p : I) : ((coin p).map not) true = σ p") (lemma := "coin_not_true") (play := "a=not; x>a.0; a>out") (uses := "map_not_true, coin_false, map_true, Bool.not_true, Bool.not_false, Bool.cond_false, Bool.cond_true, zero_add, map_bool, beq_true, coin_true, coin_total, add_zero, mul_zero, rw, -rfl")
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
*Now the proof.* The boss of *DiscreteMeasure*, for the coin.
:::

:::proofde
*Jetzt der Beweis.* Der Endgegner von *DiscreteMeasure*, für die Münze.
:::
:::solution
```
rw [map_not_true, coin_false]
```
:::
:::solution
```
rw [map_true]
rw [Bool.not_true, Bool.not_false]
rw [Bool.cond_false, Bool.cond_true, zero_add]
rw [coin_false]
```
:::
:::solution
```
rw [map_bool, beq_true, beq_true, Bool.not_true, Bool.not_false, Bool.cond_false, Bool.cond_true, zero_add, coin_false]
```
:::
:::::

:::::leanonly (proof := "(p : I) : (coin p).map not = coin ⟦σ p ‖ p, σ p⟧") (lemma := "coin_not") (uses := "bool_ext, map_true, Bool.not_true, Bool.not_false, Bool.cond_false, Bool.cond_true, zero_add, coin_false, coin_true, eq_coin, coin_not_true, add_zero, mul_zero, coin_total, apply, exact, rw")
::::hint (anchor := "gap")
:::en
Flip the coin `p`: what is its mass at `true` now?
:::

:::de
Dreh die Münze `p` um: Was ist jetzt ihre Masse bei `true`?
:::
::::

:::en
*Boss: flip the coin.* Not just the mass at `true`: the whole coin.
:::

:::de
*Endgegner: Dreh die Münze um.* Nicht nur die Masse bei `true`: die ganze Münze.
:::

:::proofen
Flipping turns the coin `p` into the coin $`1 - p`: the whole coin, not only its mass at `true`.
Your result becomes the lemma `coin_not`, which the next worlds use all the time.
:::

:::proofde
Umdrehen macht aus der Münze $`p` die Münze $`1 - p`: die ganze Münze, nicht nur ihre Masse bei
`true`. Dein Ergebnis wird das Lemma `coin_not`, das die nächsten Welten ständig benutzen.
:::
:::solution
```
apply bool_ext
rw [map_true]
rw [Bool.not_true, Bool.not_false]
rw [Bool.cond_false, Bool.cond_true, zero_add]
rw [coin_false, coin_true]
```
:::
:::solution
```
apply eq_coin
rw [map_true, Bool.not_true, Bool.not_false, Bool.cond_false, Bool.cond_true, zero_add, coin_false]
```
:::
:::solution
```
apply eq_coin
exact coin_not_true p
```
:::
:::solution
```
apply bool_ext
rw [coin_not_true, coin_true]
```
:::
:::::
