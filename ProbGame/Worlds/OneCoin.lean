import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Coins" =>

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

:::en
Then the circuits of *Bool*, with a coin at each input: `x ← coin p`, `y ← coin p`, …,
all with the same $`p` and thrown independently of each other. Then the output is random too: its
distribution is the target. Each row of the truth table has a mass, the product of the masses of its
inputs ($`p` for `true`, $`1 - p` for `false`): with two coins, `true`–`true` has mass $`p^2`,
`true`–`false` $`p(1 - p)`, and so on. The mass of the output at a value is the sum over the rows
where the output has that value. The output box below shows the target and your output, as masses and
as a small histogram (the target dashed); beside the board the bars.

A coin may go into several gates; then the results depend on each other, and the game takes that into
account.
:::

:::proofen
The circuit, read from top to bottom, is a `do` block in Lean: each coin a line `let x ← coin p`,
which *draws* `x` from the distribution `coin p`, and at the end `pure (…)`, a sure result, with what
the gates compute. The proofs learn the rules of `do` blocks one at a time, when a level needs them;
first, what a `do` block is.
:::

:::de
Dann die Schaltungen aus *Bool*, mit einer Münze an jedem Eingang: `x ← coin p`,
`y ← coin p`, …, alle mit demselben $`p` und unabhängig voneinander geworfen. Dann ist auch der Ausgang
zufällig: Seine Verteilung ist das Ziel. Jede Zeile der Wahrheitstafel hat eine Masse, das Produkt der
Massen ihrer Eingänge ($`p` für `true`, $`1 - p` für `false`): Bei zwei Münzen hat `true`–`true` die
Masse $`p^2`, `true`–`false` $`p(1 - p)`, und so weiter. Die Masse des Ausgangs bei einem Wert ist die
Summe über die Zeilen, in denen der Ausgang diesen Wert hat. Der Ausgabekasten unten zeigt Ziel und
Ausgang, als Massen und als kleines Histogramm (das Ziel gestrichelt); neben dem Spielfeld die Säulen.

Eine Münze darf in mehrere Bausteine gehen; dann hängen die Ergebnisse voneinander ab, und das Spiel
berücksichtigt das.
:::

:::proofde
Die Schaltung, von oben nach unten gelesen, ist ein `do`-Block in Lean: jede Münze eine Zeile
`let x ← coin p`, die `x` aus der Verteilung `coin p` *zieht*, und am Ende `pure (…)`, ein sicheres
Ergebnis, mit dem, was die Bausteine rechnen. Die Beweise lernen die Regeln der `do`-Blöcke eine nach
der anderen, wenn ein Level sie braucht; zuerst, was ein `do`-Block ist.
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

:::::leanonly (proof := ": coin 1 = ⟦pure true ‖ pure true, pure false⟧") (lemma := "coin_one") (uses := "bool_ext, coin_true, pure_true, Bool.cond_true, mass_one, coin_false, coin_total, Bool.cond_false, apply, rw")
::::hint (anchor := "item:mass_one")
:::en
`↑1` in the goal is `↑(1 : I)`, the number one of `I` as a mass: `mass_one` makes it `1`.
:::

:::de
`↑1` im Ziel ist `↑(1 : I)`, die Zahl eins aus `I` als Masse: `mass_one` macht daraus `1`.
:::
::::

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
:::::

::::circuit (height := "540") (inputs := "x") (gates := "not, alwaysT") (coins := "p") (target := "pure false") (context := "Lean/Rules.lean") (proof := "(p : I) : ((coin p).map (fun _ => true)).map not = pure false") (play := "a=alwaysT; b=not; x>a.0; a>b.0; b>out") (uses := "map_map, bool_ext, map_true, Bool.not_true, Bool.cond_false, zero_add, pure_true, map_not_true, map_bool, Bool.true_beq, Bool.not_false, Bool.cond_true, add_zero, mul_zero, apply, rw")
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
Two moves are one (`map_map`, from *DiscreteMeasure*); or compare the masses at `true` (`bool_ext`) right away. The last gate is `not`: your lemma `map_not_true` from
*DiscreteMeasure*. Before it, *always `true`* sends no mass to `false`: `map_bool`.
:::

:::proofde
Zwei Züge sind einer (`map_map`, aus *DiscreteMeasure*); oder vergleiche gleich die Massen bei `true` (`bool_ext`). Der letzte Baustein ist `not`: dein Lemma
`map_not_true` aus *DiscreteMeasure*. Davor schickt *immer `true`* keine Masse nach `false`: `map_bool`.
:::
:::solution
```
rw [map_map]
apply bool_ext
rw [map_true, Bool.not_true, Bool.cond_false, Bool.cond_false, zero_add, pure_true, Bool.cond_false]
```
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

:::::circuit (height := "440") (inputs := "x") (gates := "not") (coins := "p") (target := "bool true:1-p false:p") (context := "Lean/Rules.lean") (proof := "(p : I) : (coin p).map not = coin ⟦σ p ‖ p, σ p⟧") (lemma := "coin_not") (play := "a=not; x>a.0; a>out") (uses := "eq_coin, map_not_true, coin_false, bool_ext, coin_true, map_true, Bool.not_true, Bool.not_false, Bool.cond_false, Bool.cond_true, zero_add, coin_total, add_zero, mul_zero, apply, rw")
::::hint (anchor := "gap")
:::en
Flip the coin `p`: what is its mass at `true` now?
:::

:::de
Dreh die Münze `p` um: Was ist jetzt ihre Masse bei `true`?
:::
::::

:::en
*Flip the coin.* The coin `x` is thrown at the top; below, the output with the target: `false`
with mass $`p`, `true` with $`1 - p`. Put a `not` between them: the mass at `true` came from `false`.
:::

:::de
*Dreh die Münze um.* Oben wird die Münze `x` geworfen; unten der Ausgang mit dem Ziel:
`false` mit Masse $`p`, `true` mit $`1 - p`. Setz ein `nicht` dazwischen: Die Masse bei `true` kam
von `false`.
:::

:::proofen
Flipping turns the coin `p` into the coin $`1 - p`: the whole coin, not only its mass at `true`. A
distribution on `Bool` is a coin (`eq_coin`), and its mass at `true` is `map_not_true` from *DiscreteMeasure*.
Your result becomes the lemma `coin_not`, which the next worlds use all the time.
:::

:::proofde
Umdrehen macht aus der Münze $`p` die Münze $`1 - p`: die ganze Münze, nicht nur ihre Masse bei
`true`. Eine Verteilung auf `Bool` ist eine Münze (`eq_coin`), und ihre Masse bei `true` ist
`map_not_true` aus *DiscreteMeasure*. Dein Ergebnis wird das Lemma `coin_not`, das die nächsten Welten
ständig benutzen.
:::
:::solution
```
apply eq_coin
rw [map_not_true, coin_false]
```
:::
:::solution
```
apply bool_ext
rw [map_not_true, coin_false, coin_true]
```
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
:::::

:::::circuit (height := "440") (inputs := "x y") (gates := "") (coins := "p p") (target := "bool true:p false:1-p") (start := "a=and; a>out") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; pure (x && x)) = coin p") (new := "bind_pure") (play := "x>a.0; x>a.1") (uses := "Bool.and_self, bind_pure, pure_bind, exact, rw, simp_rw")
::::hint (anchor := "statement")
:::en
`x` is not a random variable: it is the name of one draw from `coin p`, and the whole `do` block is a
distribution.
:::

:::de
`x` ist keine Zufallsvariable: Es ist der Name eines Zugs aus `coin p`, und der ganze `do`-Block ist
eine Verteilung.
:::
::::

:::en
*One draw, used twice.* An `and` lies on the board already, and the target is the coin itself:
`true` with $`p`.
:::

:::de
*Ein Zug, zweimal benutzt.* Ein `and` liegt schon auf dem Spielfeld, und das Ziel ist die Münze
selbst: `true` mit $`p`.
:::

:::proofen
On the board, the coin `x` went into the `and` twice; in Lean that is `x && x`. `x` is the name of
one draw from `coin p`, not a random variable: used twice, it is the same value twice. Two coins `x`
and `y` would be two draws, with $`p^2` (soon, in `coin_and`). What is left, draw `x` and give it
back, is `coin p` itself.

New: the rule `bind_pure : (do let x ← μ; pure x) = μ`. The `x` of `let x ← coin p` is bound, as the
`x` of `fun x => …` in *DiscreteMeasure*. (Lean itself reads `do let x ← μ; pure x` as `μ` at once, when you
type it.)
:::

:::proofde
Auf dem Spielfeld ging die Münze `x` zweimal ins `and`; in Lean ist das `x && x`. `x` ist der Name
eines Zugs aus `coin p`, keine Zufallsvariable: Zweimal benutzt ist es zweimal derselbe Wert. Zwei
Münzen `x` und `y` wären zwei Züge, mit $`p^2` (bald, in `coin_and`). Was bleibt, `x` ziehen und
zurückgeben, ist `coin p` selbst.

Neu: die Regel `bind_pure : (do let x ← μ; pure x) = μ`. Das `x` von `let x ← coin p` ist gebunden,
wie das `x` von `fun x => …` in *DiscreteMeasure*. (Lean selbst liest `do let x ← μ; pure x` sofort als
`μ`, wenn du es eintippst.)
:::
:::solution
```
simp_rw [Bool.and_self, bind_pure]
```
:::
:::solution
```
simp_rw [Bool.and_self]
rw [bind_pure]
```
:::
:::solution
```
simp_rw [Bool.and_self]
exact bind_pure (coin p)
```
:::
:::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) (f : Bool → DiscreteMeasure Bool) : (do let x ← μ; f x) = μ.bind f") (uses := "rfl")
:::en
*`do` is `bind`.* `do let x ← μ; f x` draws `x` from `μ` and goes on with `f x`: `f` says, for each
result of the first draw, how to go on. As a distribution, this is `μ.bind f`, as `Measure.bind` for
measures. `do` is only a way to write it, easier to read when several draws follow each other.
:::

:::de
*`do` ist `bind`.* `do let x ← μ; f x` zieht `x` aus `μ` und macht mit `f x` weiter: `f` sagt für
jedes Ergebnis des ersten Zugs, wie es weitergeht. Als Verteilung ist das `μ.bind f`, wie
`Measure.bind` für Maße. `do` ist nur eine Schreibweise dafür, leichter zu lesen, wenn mehrere Züge
aufeinander folgen.
:::

:::proofen
Both sides are the same, only written differently.
:::

:::proofde
Beide Seiten sind dasselbe, nur anders geschrieben.
:::
:::solution
```
rfl
```
:::
::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) (f : Bool → DiscreteMeasure Bool) : (do let x ← μ; f x) true = μ true * f true true + μ false * f false true") (new := "bind_apply") (lemma := "bind_true") (board := "bind") (uses := "bind_apply, Fintype.sum_bool, exact, rw, simp_rw")
:::en
*Two ways to true.* The mass of `do let x ← μ; f x` at `true` comes two ways: the first draw is
`true`, or it is `false`. On the board, `coin p` is thrown first; then a second coin, at `T` when
the first showed `true`, at `F` else. The way through `T` has weight $`p`, the way through `F`
$`1 - p`; each times the mass at `true` of the coin thrown then. Fill in these masses for each of the
four second coins.
:::

:::de
*Zwei Wege zu true.* Die Masse von `do let x ← μ; f x` bei `true` kommt auf zwei Wegen: Der erste
Zug ist `true`, oder er ist `false`. Auf dem Spielfeld wird zuerst `coin p` geworfen, dann eine
zweite Münze: die bei `T`, wenn die erste `true` zeigte, sonst die bei `F`. Der Weg über `T` hat das
Gewicht $`p`, der über `F` $`1 - p`; jeweils mal die Masse bei `true` der Münze, die dann geworfen
wird. Trag diese Massen für jede der vier zweiten Münzen ein.
:::

:::proofen
The definition of a draw sums over the first draw `a`: its mass, times the mass of what follows,

```
(do let a ← μ; f a) b = ∑' a, μ a * (f a) b
```

On a finite type, `∑'` is the finite sum `∑`, and that is the new rule
`bind_apply : (do let a ← μ; f a) b = ∑ a, μ a * f a b`. On `Bool` it has two summands
(`Fintype.sum_bool`). What you prove is unlocked as `bind_true`.
:::

:::proofde
Die Definition eines Zugs summiert über den ersten Zug `a`: seine Masse, mal die Masse dessen, was
folgt,

```
(do let a ← μ; f a) b = ∑' a, μ a * (f a) b
```

Auf einem endlichen Typ ist `∑'` die endliche Summe `∑`, und das ist die neue Regel
`bind_apply : (do let a ← μ; f a) b = ∑ a, μ a * f a b`. Auf `Bool` hat sie zwei Summanden
(`Fintype.sum_bool`). Was du beweist, wird als `bind_true` freigeschaltet.
:::
:::solution
```
rw [bind_apply, Fintype.sum_bool]
```
:::
:::solution
```
simp_rw [bind_apply, Fintype.sum_bool]
```
:::
:::solution
```
rw [bind_apply]
exact Fintype.sum_bool _
```
:::
::::

:::::circuit (height := "440") (inputs := "x y") (gates := "and, or, not") (coins := "p p") (target := "bool true:2p-p^2 false:(1-p)^2") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure (x || y)) true = (↑p + ↑(σ p) * ↑p : ℝ≥0∞)") (play := "a=or; x>a.0; y>a.1; a>out") (new := "simp") (uses := "bind_true, coin_true, coin_false, coin_total, rw, simp, simp_rw")
::::hint (anchor := "item:simp")
:::en
`simp`: the simplifier, with all rules marked simp.
:::

:::de
`simp`: der Simplifier, mit allen Regeln, die simp tragen.
:::
::::

:::en
*At least one true.* Split by the first coin: two ways to `true`.
:::

:::de
*Mindestens einmal true.* Nach der ersten Münze geteilt: zwei Wege zu `true`.
:::

:::proofen
The right side is the two ways: `bind_true`, once for each draw. What is left is computing, and from
now on the simplifier does it: `simp` rewrites with a whole list of rules, again and again, until
none applies any more, and it computes with numbers.

Which rules are in the list? In the inventory they now carry the mark *simp*: rules that you proved
or were given, such as `zero_add`, `add_zero`, `mul_one` and `Bool.true_and`. Not in the list are
rules like `bool_ext`, `map_true`, `mass_not` or `add_comm`: they change what you prove, or could go
on forever, and you apply them yourself. `simp [h]` puts a rule `h` into the list for this one call.
:::

:::proofde
Die rechte Seite sind die zwei Wege: `bind_true`, einmal für jeden Zug. Was bleibt, ist Rechnen, und
das macht ab jetzt der Simplifier: `simp` schreibt mit einer ganzen Liste von Regeln um, immer
wieder, bis keine mehr passt, und er rechnet mit Zahlen.

Welche Regeln stehen in der Liste? Im Inventar tragen sie jetzt die Marke *simp*: Regeln, die du
bewiesen oder bekommen hast, etwa `zero_add`, `add_zero`, `mul_one` und `Bool.true_and`. Nicht in der Liste
sind Regeln wie `bool_ext`, `map_true`, `mass_not` oder `add_comm`: Sie ändern, was du beweist, oder
könnten endlos laufen, und du wendest sie selbst an. `simp [h]` nimmt eine Regel `h` für diesen
einen Aufruf in die Liste auf.
:::
:::solution
```
rw [bind_true, bind_true, bind_true]
simp
```
:::
:::solution
```
simp_rw [bind_true]
simp
```
:::
:::solution
```
simp [bind_true]
```
:::
:::solution
```
rw [bind_true, bind_true, bind_true]
rw [coin_true, coin_false]
simp
```
:::
:::::

::::quiz (tactic := "simp") (statements := "(p : I) : coin p true = ↑p ;; (p : I) : (coin p).map not = coin (σ p) ;; (b : Bool) : (pure b : DiscreteMeasure Bool) true + (pure b : DiscreteMeasure Bool) false = 1 ;; (p : I) : coin p true + coin p false = 1 ;; (x : Bool) : (x && !x) = false ;; (x y : Bool) : (x && y) = (y && x)") (answer := "1, 4, 5") (context := "Lean/Rules.lean") (group := "chance")
:::en
*Which ones?* `simp` rewrites with the rules marked simp, until none applies. Which of these
statements does it prove?
:::

:::de
*Welche?* `simp` schreibt mit den Regeln um, die die Marke simp tragen, bis keine mehr passt. Welche
dieser Aussagen beweist es?
:::
::::

:::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] (f : Bool → Bool) : μ.map f = (do let x ← μ; ⟦pure (f x) ‖ pure (f x), pure x, μ.map f⟧)") (lemma := "map_eq_pure_bind") (uses := "map_bool, bind_apply, Fintype.sum_bool, pure_apply, bool_ext, map_true, bind_true, <;>, apply, cases, ext, rw, simp, simp_rw")
::::hint (anchor := "statement")
:::en
A move `μ.map f` is a `do` block: draw `x` from `μ`, then `f x` for sure.
:::

:::de
Ein Zug `μ.map f` ist ein `do`-Block: `x` aus `μ` ziehen, dann sicher `f x`.
:::
::::

:::en
*A move is a `do` block.* A move `μ.map f` draws `x` from `μ` and computes `f x`, for sure.
:::

:::de
*Ein Zug ist ein `do`-Block.* Ein Zug `μ.map f` zieht `x` aus `μ` und rechnet `f x` aus, sicher.
:::

:::proofen
Compare the masses at every `b`, with `map_bool` and the definition `bind_apply`. What `f` does is
unknown, and so is `b`: eight cases, and in each `simp` computes. You prove it on `Bool`; it holds
for every type, and it is unlocked as `map_eq_pure_bind` in this general form.
:::

:::proofde
Vergleiche die Massen bei jedem `b`, mit `map_bool` und der Definition `bind_apply`. Was `f` tut,
ist unbekannt, und `b` auch: acht Fälle, und in jedem rechnet `simp`. Du beweist es auf `Bool`; es
gilt für jeden Typ und wird in dieser allgemeinen Form als `map_eq_pure_bind` freigeschaltet.
:::
:::solution
```
ext b
rw [map_bool, bind_apply]
simp_rw [Fintype.sum_bool, pure_apply]
cases f true <;> cases f false <;> cases b <;> simp
```
:::
:::solution
```
apply bool_ext
rw [map_true, bind_true]
cases f true <;> cases f false <;> simp
```
:::
:::solution
```
ext b
rw [map_bool, bind_apply, Fintype.sum_bool]
cases b <;> simp <;> cases f true <;> cases f false <;> simp
```
:::
:::solution
```
apply bool_ext
simp [map_true, bind_true]
cases f true <;> cases f false <;> simp
```
:::
:::::

:::::circuit (height := "440") (inputs := "x") (gates := "not, and, or") (coins := "p") (target := "bool true:1-p false:p") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; pure (!x)) = coin (σ p)") (play := "a=not; x>a.0; a>out") (uses := "map_eq_pure_bind, coin_not, bool_ext, bind_true, eq_coin, apply, rw, simp")
:::en
*A gate is a draw.* One coin, one `not`.
:::

:::de
*Ein Baustein ist eine Ziehung.* Eine Münze, ein `not`.
:::

:::proofen
Your law `map_eq_pure_bind`, read the other way round: a `do` block that only applies a gate is a move.
:::

:::proofde
Dein Gesetz `map_eq_pure_bind`, andersherum gelesen: Ein `do`-Block, der nur einen Baustein anwendet, ist ein Zug.
:::
:::solution
```
rw [← map_eq_pure_bind, coin_not]
```
:::
:::solution
```
apply bool_ext
rw [bind_true]
simp
```
:::
:::solution
```
apply eq_coin
rw [bind_true]
simp
```
:::
:::solution
```
rw [← coin_not, map_eq_pure_bind]
```
:::
:::::

::::circuit (height := "440") (inputs := "x y") (gates := "and, or, not") (coins := "p p") (target := "bool true:p^2 false:1-p^2") (context := "Lean/Rules.lean") (proof := "(p q : I) : (do let x ← coin p; let y ← coin q; pure (x && y)) = coin (p * q)") (lemma := "coin_and") (play := "a=and; x>a.0; y>a.1; a>out") (uses := "bool_ext, bind_true, mass_mul, eq_coin, apply, rw, simp")
:::en
*Both `true`.* Two coins, and `true` only when both show `true`.
:::

:::de
*Beide `true`.* Zwei Münzen, und `true` nur, wenn beide `true` zeigen.
:::

:::proofen
Your circuit, read from top to bottom, is a `do` block: `let x ← coin p` throws a coin and calls its
result `x`, and `pure` at the end is the result. Each `←` is a new throw, independent of the others.
Prove it for two coins `p` and `q` (on the board both were `p`): both `true` with probability
$`p \cdot q`. It becomes your lemma `coin_and`, independence itself.

Compare the masses at `true`; every draw splits into its two ways (`bind_true`). The rule
`mass_mul : ↑(p * q) = ↑p * ↑q` from *ENNReal* carries no mark simp: `simp [h]` takes a rule `h` along for one call.
:::

:::proofde
Dein Schaltplan, von oben nach unten gelesen, ist ein `do`-Block: `let x ← coin p` wirft eine Münze
und nennt ihr Ergebnis `x`, und `pure` am Ende ist das Ergebnis. Jedes `←` ist ein neuer Wurf,
unabhängig von den anderen. Beweise es für zwei Münzen `p` und `q` (auf dem Spielfeld waren beide
`p`): beide `true` mit Wahrscheinlichkeit $`p \cdot q`. Es wird dein Lemma `coin_and`, die
Unabhängigkeit selbst.

Vergleiche die Massen bei `true`; jeder Zug teilt sich in seine zwei Wege (`bind_true`). Die Regel
`mass_mul : ↑(p * q) = ↑p * ↑q` aus *ENNReal* trägt keine Marke simp: `simp [h]` nimmt eine Regel `h` für einen Aufruf mit.
:::
:::solution
```
apply bool_ext
rw [bind_true, bind_true, bind_true]
simp [mass_mul]
```
:::
:::solution
```
apply eq_coin
rw [bind_true, bind_true, bind_true]
simp [mass_mul]
```
:::
:::solution
```
apply bool_ext
simp [bind_true, mass_mul]
```
:::
:::solution
```
apply bool_ext
rw [bind_true, bind_true, bind_true]
simp
rw [mass_mul]
```
:::
::::

::::leanonly (proof := "(a b : ℝ≥0∞) : a * b + b * a = 2 * a * b") (new := "ring") (uses := "ring")
:::en
*The same product twice.* `a * b` and `b * a` are the same number. The simplifier does not use that:
it would turn the product round for ever.
:::

:::de
*Zweimal dasselbe Produkt.* `a * b` und `b * a` sind dieselbe Zahl. Der Simplifier benutzt das nicht:
Er würde das Produkt endlos umdrehen.
:::

:::proofen
A new tactic: `ring` proves an equation that holds by computing with `+`, `*` and powers alone,
whatever the letters are: the order of factors and summands, brackets, multiplying out. It uses no
hypothesis and no rule of the game, only the laws of computing, and it does not know what a coin or a
mass is. So first the rules of the game, with `rw` and `simp`; then `ring` for what is left.
:::

:::proofde
Eine neue Taktik: `ring` beweist eine Gleichung, die allein durch Rechnen mit `+`, `*` und Potenzen
gilt, was auch immer die Buchstaben sind: die Reihenfolge von Faktoren und Summanden, Klammern,
Ausmultiplizieren. Sie benutzt keine Annahme und keine Regel des Spiels, nur die Rechengesetze, und
sie weiß nicht, was eine Münze oder eine Masse ist. Also zuerst die Regeln des Spiels, mit `rw` und
`simp`; dann `ring` für den Rest.
:::
:::solution
```
ring
```
:::
::::

::::circuit (inputs := "x y") (gates := "and, or, not") (coins := "p p") (target := "bool true:2p(1-p) false:p^2+(1-p)^2") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure ((x || y) && !(x && y))) true = (2 * ↑p * ↑(σ p) : ℝ≥0∞)") (play := "a=or; b=and; c=not; d=and; x>a.0; y>a.1; x>b.0; y>b.1; b>c.0; a>d.0; c>d.1; d>out") (uses := "bind_true, coin_true, coin_false, coin_total, ring, rw, simp, simp_rw")
:::en
*Boss: exactly one `true`*, without a function for it: at least one, but not both.
:::

:::de
*Endgegner: genau einmal `true`*, ohne eine Funktion dafür: mindestens einmal, aber nicht beide.
:::

:::proofen
*With which mass?* Not the whole distribution this time: its mass at `true`, computed.
:::

:::proofde
*Mit welcher Masse?* Diesmal nicht die ganze Verteilung: ihre Masse bei `true`, ausgerechnet.
:::
:::solution
```
rw [bind_true, bind_true, bind_true]
simp
ring
```
:::
:::solution
```
simp_rw [bind_true]
simp
ring
```
:::
:::solution
```
simp [bind_true]
ring
```
:::
:::solution
```
rw [bind_true, bind_true, bind_true]
rw [coin_true, coin_false]
simp
ring
```
:::
::::
