import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Circuits" =>

%%%
htmlSplit := .never
number := false
%%%

:::en
Maps built from gates, as circuits are. The inputs are above, the output below. Drag gates from the side onto the board (or tap them), and draw wires: from an output,
the dot below a block, to an input, the circle above one (tap the one and then the other, or drag).
The target is a *truth table*: the output for every row of inputs, a column in the box below. Tap a
column, and its values are on the board.

Each level has a second half in Lean: there your circuit is a function of its inputs, and the
statement says that it is the target table. The Lean half is short here; it grows in the worlds that
follow.
:::

:::de
Abbildungen, gebaut aus Bausteinen, wie Schaltungen. Die Eingänge sind oben, der Ausgang unten. Zieh Bausteine vom Rand aufs Spielfeld (oder tippe sie an) und ziehe
Drähte: von einem Ausgang, dem Punkt unter einem Baustein, zu einem Eingang, dem Kreis darüber (tippe
den einen und dann den anderen an, oder zieh). Das Ziel ist eine *Wahrheitstafel*: der Ausgang für
jede Zeile der Eingänge, eine Spalte im Kasten unten. Tippe eine Spalte an, und ihre Werte stehen auf
dem Spielfeld.

Jedes Level hat eine zweite Hälfte in Lean: Dort ist deine Schaltung eine Funktion ihrer Eingänge,
und die Aussage sagt, dass sie die Zieltafel ist. Die Lean-Hälfte ist hier kurz; sie wächst in den
Welten danach.
:::

::::circuit (height := "300") (inputs := "x") (gates := "") (table := "01") (goal := "x") (shape := "x") (proof := "(x : Bool) : x = x") (new := "rfl") (play := "x>out")
:::en
*A wire.* The output is to be the input itself. Wire `x` to the output: tap `x`, then the output.
:::

:::de
*Ein Draht.* Der Ausgang soll der Eingang selbst sein. Verdrahte `x` mit dem Ausgang: Tippe `x` an,
dann den Ausgang.
:::

:::proofen
In Lean the board reads: the output, `x`, is the target, `x`. How to read a statement:
`example (x : Bool) : x = x` says *for every `x` of type `Bool`, `x = x`*. Before the colon stand the
variables (and later the hypotheses), after it what is claimed. Below the statement Lean shows the
*goal*: the variables and hypotheses on top, and after `⊢` what is still to be shown. A *tactic*, one
line, changes the goal, until nothing is left. The tactic `rfl` proves an equation whose two sides are
the same.

*Tip.* `rfl`.
:::

:::proofde
In Lean liest sich das Spielfeld so: Der Ausgang, `x`, ist das Ziel, `x`. So liest man eine Aussage:
`example (x : Bool) : x = x` sagt *für jedes `x` vom Typ `Bool` ist `x = x`*. Vor dem Doppelpunkt
stehen die Variablen (und später die Annahmen), danach das, was behauptet wird. Unter der Aussage zeigt
Lean das *Ziel*: oben die Variablen und Annahmen, und nach `⊢` das, was noch zu zeigen ist. Eine
*Taktik*, eine Zeile, ändert das Ziel, bis nichts mehr übrig ist. Die Taktik `rfl` beweist eine
Gleichung, deren beide Seiten gleich sind.

*Tipp.* `rfl`.
:::
:::solution
```
rfl
```
:::
::::

::::circuit (height := "400") (inputs := "true") (gates := "not") (table := "0") (goal := "false") (shape := "!true") (proof := ": (!true) = false") (lemma := "Bool.not_true") (play := "a=not; true>a.0; a>out")
:::en
*Not true.* The input is `true` itself, the target `false`. Drag `not` onto the board, then wire
`true` to it and it to the output.
:::

:::de
*Nicht true.* Der Eingang ist `true` selbst, das Ziel `false`. Zieh `nicht` aufs Spielfeld, dann
verdrahte `true` mit ihm und ihn mit dem Ausgang.
:::

:::proofen
Now the two sides are not the same as they stand: `!true` on the left, `false` on the right. But
`rfl` also *reduces*: it computes with the definitions. `not` is defined by its two cases,

`fun | true => false | false => true`

(a function given by cases: `true` goes to `false`, `false` to `true`). Here Lean knows the value,
`true`, so it takes that case: `!true` reduces to `false`. Then both sides are the same.

*Tip.* `rfl`.
:::

:::proofde
Jetzt sind die beiden Seiten nicht so, wie sie dastehen, gleich: links `!true`, rechts `false`. Aber
`rfl` *reduziert* auch: Es rechnet mit den Definitionen. `not` ist durch seine zwei Fälle definiert,

`fun | true => false | false => true`

(eine Funktion, durch Fälle gegeben: `true` geht nach `false`, `false` nach `true`). Hier kennt Lean
den Wert, `true`, also nimmt es diesen Fall: `!true` reduziert zu `false`. Danach sind beide Seiten
gleich.

*Tipp.* `rfl`.
:::
:::solution
```
rfl
```
:::
::::

::::leanonly (proof := ": (!false) = true") (lemma := "Bool.not_false") (context := "Lean/WorldBool.lean") (group := "bool")
:::en
*Not false.* The other half of `not`, in Lean only: the level before proved `(!true) = false`, the
rule `Bool.not_true`.
:::

:::de
*Nicht false.* Die andere Hälfte von `not`, nur in Lean: Das Level davor hat `(!true) = false`
bewiesen, die Regel `Bool.not_true`.
:::

:::proofen
`not` is defined by its two cases, and here Lean knows the value: `!false` reduces to `true`.

*Tip.* `rfl`.
:::

:::proofde
`not` ist durch seine zwei Fälle definiert, und hier kennt Lean den Wert: `!false` reduziert zu
`true`.

*Tipp.* `rfl`.
:::
:::solution
```
rfl
```
:::
::::

::::circuit (height := "500") (inputs := "x") (gates := "not") (table := "01") (goal := "x") (shape := "!(!x)") (start := "a=not; x>a.0") (proof := "(x : Bool) : (!(!x)) = x") (lemma := "Bool.not_not") (new := "cases") (play := "b=not; a>b.0; b>out")
:::en
*Flipped twice.* One `not` is already on the board and stays there. Add a second one, so that the output is the input again.
:::

:::de
*Zweimal umgedreht.* Ein `nicht` liegt schon auf dem Spielfeld und bleibt dort. Füge ein zweites hinzu, sodass der Ausgang wieder der Eingang ist.
:::

:::proofen
`!(!x) = x` for every `x`. Now `rfl` does not help: `not` is defined by its cases, and Lean cannot
reduce `!x` as long as it does not know `x`. The tactic `cases x` splits into the cases `false` and
`true`, two goals one after the other, as the two rows of the table. In each, both sides reduce to
the same: `!(!false)` to `!true` and then to `false`. Your result becomes the lemma `Bool.not_not`, as
it is called in Lean.

*Tip.* `cases x`, then `rfl`, `rfl`.
:::

:::proofde
`!(!x) = x` für jedes `x`. Jetzt hilft `rfl` nicht: `not` ist durch seine Fälle definiert, und Lean
kann `!x` nicht reduzieren, solange es `x` nicht kennt. Die Taktik `cases x` teilt in die Fälle
`false` und `true`, zwei Ziele nacheinander, wie die zwei Zeilen der Tafel. In jedem reduzieren beide
Seiten zum selben: `!(!false)` zu `!true` und dann zu `false`. Dein Ergebnis wird das Lemma
`Bool.not_not`, wie es in Lean heißt.

*Tipp.* `cases x`, dann `rfl`, `rfl`.
:::
:::solution
```
cases x
rfl
rfl
```
:::
::::

::::circuit (height := "500") (inputs := "x") (gates := "not, or") (table := "11") (goal := "true") (proof := "(x : Bool) : (x || !x) = (bif x then true else true)") (new := "<;>") (play := "a=not; b=or; x>a.0; x>b.0; a>b.1; b>out")
:::en
*Always true, without always true.* An output can feed several inputs: wire `x` twice.
:::

:::de
*Immer true, ohne immer true.* Ein Ausgang kann mehrere Eingänge speisen: Verdrahte `x` zweimal.
:::

:::proofen
How to read the statement: on the left your circuit, `x || !x`; on the right the target, the table
written as a decision: `bif x then true else true` is `true` when `x` is `true`, else `true` (`bif`
is *if* for a `Bool`; it reduces as soon as `x` is known). `||` is defined by cases of its left side:
`false || b` reduces to `b`, and `true || b` to `true`. So `cases x`, then `rfl` in each case. New:
`t₁ <;> t₂` runs `t₂` on every goal that `t₁` leaves, in one line: `cases x <;> rfl`.

*Tip.* `cases x <;> rfl`.
:::

:::proofde
So liest man die Aussage: links deine Schaltung, `x || !x`; rechts das Ziel, die Tafel als
Entscheidung geschrieben: `bif x then true else true` ist `true`, wenn `x` `true` ist, sonst `true`
(`bif` ist *wenn* für ein `Bool`; es reduziert, sobald `x` bekannt ist). `||` ist durch Fälle seiner linken Seite definiert:
`false || b` reduziert zu `b`, und `true || b` zu `true`. Also `cases x`, dann `rfl` in jedem Fall. Neu:
`t₁ <;> t₂` führt `t₂` auf jedem Ziel aus, das `t₁` übrig lässt, in einer Zeile: `cases x <;> rfl`.

*Tipp.* `cases x <;> rfl`.
:::
:::solution
```
cases x <;> rfl
```
:::
::::

::::circuit (inputs := "x y") (gates := "and, or, not") (table := "0110") (goal := "x ^^ y") (proof := "(x y : Bool) : ((x || y) && !(x && y)) = (bif x then (bif y then false else true) else (bif y then true else false))") (play := "a=or; b=and; c=not; d=and; x>a.0; y>a.1; x>b.0; y>b.1; b>c.0; a>d.0; c>d.1; d>out")
:::en
*The boss: exactly one.* Two inputs now, and four rows: one for each pair of values. `true` when exactly one
input is `true`: at least one, but not both. In Lean this is `xor`, written `x ^^ y`.
:::

:::de
*Der Endgegner: genau eines.* Jetzt zwei Eingänge und vier Zeilen: eine für jedes Paar von Werten. `true`, wenn
genau ein Eingang `true` ist: mindestens einer, aber nicht beide. In Lean ist das `xor`, geschrieben
`x ^^ y`.
:::

:::proofen
The table has four rows now, one for each pair of values: first `x` decides, then `y`, a `bif` in
each branch of a `bif`. `cases x` makes two goals; in each, `cases y` makes two more: four goals, the
four rows. With `<;>` in one line.

*Tip.* `cases x <;> cases y <;> rfl`.
:::

:::proofde
Die Tafel hat jetzt vier Zeilen, eine für jedes Paar von Werten: erst entscheidet `x`, dann `y`, ein
`bif` in jedem Zweig eines `bif`. `cases x` macht zwei Ziele; in jedem macht `cases y` zwei weitere:
vier Ziele, die vier Zeilen. Mit `<;>` in einer Zeile.

*Tipp.* `cases x <;> cases y <;> rfl`.
:::
:::solution
```
cases x <;> cases y <;> rfl
```
:::
::::
