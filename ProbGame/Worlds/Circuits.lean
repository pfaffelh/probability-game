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
Maps with several inputs, built from gates, as circuits are. The inputs `x`, `y` are above, the
output below. Drag gates from the side onto the board (or tap them), and draw wires: from an output,
the dot below a block, to an input, the circle above one (tap the one and then the other, or drag).
The target is a *truth table*: the output for every row of inputs. Tap a row, and its coins are on
the board. In Lean your circuit is a function of `x` and `y`, and `decide +revert` checks every row.
:::

:::de
Abbildungen mit mehreren Eingängen, gebaut aus Bausteinen, wie Schaltungen. Die Eingänge `x`, `y`
sind oben, der Ausgang unten. Zieh Bausteine vom Rand aufs Spielfeld (oder tippe sie an) und ziehe
Drähte: von einem Ausgang, dem Punkt unter einem Baustein, zu einem Eingang, dem Kreis darüber (tippe
den einen und dann den anderen an, oder zieh). Das Ziel ist eine *Wahrheitstafel*: der Ausgang für
jede Zeile der Eingänge. Tippe eine Zeile an, und ihre Münzen liegen auf dem Spielfeld. In Lean ist
deine Schaltung eine Funktion von `x` und `y`, und `decide +revert` prüft jede Zeile.
:::

::::circuit (inputs := "x") (gates := "not") (table := "10") (goal := "not x") (proof := "(x : Bool) : (!x) = (not x)") (play := "a=not; x>a.0; a>out")
:::en
*A wire and a gate.* Drag `not` onto the board, then wire `x` to it and it to the output.
:::

:::de
*Ein Draht und ein Baustein.* Zieh `nicht` aufs Spielfeld, dann verdrahte `x` mit ihm und ihn mit dem
Ausgang.
:::

:::proofen
The statement is your circuit: its output, as a function of `x`, is the target. `decide +revert`
checks it for both values of `x`.

*Tip.* `decide +revert`.
:::

:::proofde
Die Aussage ist deine Schaltung: Ihr Ausgang, als Funktion von `x`, ist das Ziel. `decide +revert`
prüft das für beide Werte von `x`.

*Tipp.* `decide +revert`.
:::
:::solution
```
decide +revert
```
:::
::::

::::circuit (inputs := "x y") (gates := "and, or") (table := "0001") (goal := "x && y") (proof := "(x y : Bool) : (x && y) = (x && y)") (play := "a=and; x>a.0; y>a.1; a>out")
:::en
*Both.* The output is `true` only when both inputs are. Four rows now: one for each pair of values.
:::

:::de
*Beide.* Der Ausgang ist nur `true`, wenn beide Eingänge es sind. Jetzt vier Zeilen: eine für jedes
Paar von Werten.
:::

:::proofen
*Tip.* `decide +revert`.
:::

:::proofde
*Tipp.* `decide +revert`.
:::
:::solution
```
decide +revert
```
:::
::::

::::circuit (inputs := "x") (gates := "not, or") (table := "11") (goal := "true") (proof := "(x : Bool) : (x || !x) = (true)") (play := "a=not; b=or; x>a.0; x>b.0; a>b.1; b>out")
:::en
*Always true, without always true.* An output can feed several inputs: wire `x` twice.
:::

:::de
*Immer true, ohne immer true.* Ein Ausgang kann mehrere Eingänge speisen: Verdrahte `x` zweimal.
:::

:::proofen
*Tip.* `decide +revert`.
:::

:::proofde
*Tipp.* `decide +revert`.
:::
:::solution
```
decide +revert
```
:::
::::

::::circuit (inputs := "x y") (gates := "and, not") (table := "0111") (goal := "x || y") (proof := "(x y : Bool) : (!(!x && !y)) = (x || y)") (play := "a=not; b=not; c=and; d=not; x>a.0; y>b.0; a>c.0; b>c.1; c>d.0; d>out")
:::en
*Or, without or.* At least one `true`, with `and` and `not` only. (Not both `false`.)
:::

:::de
*Oder, ohne oder.* Mindestens einmal `true`, nur mit `und` und `nicht`. (Nicht beide `false`.)
:::

:::proofen
This is one of De Morgan's laws: `!(!x && !y) = (x || y)`.

*Tip.* `decide +revert`.
:::

:::proofde
Das ist eine der Regeln von De Morgan: `!(!x && !y) = (x || y)`.

*Tipp.* `decide +revert`.
:::
:::solution
```
decide +revert
```
:::
::::

::::circuit (inputs := "x y") (gates := "and, or, not") (table := "0110") (goal := "x ^^ y") (proof := "(x y : Bool) : ((x || y) && !(x && y)) = (x ^^ y)") (play := "a=or; b=and; c=not; d=and; x>a.0; y>a.1; x>b.0; y>b.1; b>c.0; a>d.0; c>d.1; d>out")
:::en
*Exactly one.* `true` when exactly one input is `true`: at least one, but not both. In Lean this is
`xor`, written `x ^^ y`.
:::

:::de
*Genau eines.* `true`, wenn genau ein Eingang `true` ist: mindestens einer, aber nicht beide. In Lean
ist das `xor`, geschrieben `x ^^ y`.
:::

:::proofen
*Tip.* `decide +revert`.
:::

:::proofde
*Tipp.* `decide +revert`.
:::
:::solution
```
decide +revert
```
:::
::::

::::circuit (inputs := "x y") (gates := "and, or, not, xor") (table := "1001") (goal := "x == y") (proof := "(x y : Bool) : (!(x ^^ y)) = (x == y)") (play := "a=xor; b=not; x>a.0; y>a.1; a>b.0; b>out")
:::en
*The same.* `true` when both inputs are the same: both `true`, or both `false`. New: what you built
in the last level is now a gate of its own, `xor`.
:::

:::de
*Gleich.* `true`, wenn beide Eingänge gleich sind: beide `true`, oder beide `false`. Neu: Was du im
letzten Level gebaut hast, ist jetzt ein eigener Baustein, `xor`.
:::

:::proofen
*Tip.* `decide +revert`.
:::

:::proofde
*Tipp.* `decide +revert`.
:::
:::solution
```
decide +revert
```
:::
::::

::::circuit (inputs := "x y z") (gates := "and, or") (table := "00010111") (goal := "decide (2 ≤ x.toNat + y.toNat + z.toNat)") (proof := "(x y z : Bool) : ((x && y) || (x && z) || (y && z)) = (decide (2 ≤ x.toNat + y.toNat + z.toNat))") (play := "a=and; b=and; c=and; d=or; e=or; x>a.0; y>a.1; x>b.0; z>b.1; y>c.0; z>c.1; a>d.0; b>d.1; d>e.0; c>e.1; e>out")
:::en
*The boss: the majority of three.* `true` when at least two of the three inputs are. Eight rows.
In Lean the target counts: `x.toNat` is `1` for `true` and `0` for `false`.
:::

:::de
*Der Endgegner: die Mehrheit von dreien.* `true`, wenn mindestens zwei der drei Eingänge es sind.
Acht Zeilen. In Lean zählt das Ziel: `x.toNat` ist `1` für `true` und `0` für `false`.
:::

:::proofen
*Tip.* `decide +revert`: eight rows.
:::

:::proofde
*Tipp.* `decide +revert`: acht Zeilen.
:::
:::solution
```
decide +revert
```
:::
::::
