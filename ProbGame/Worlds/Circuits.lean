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

::::circuit (inputs := "x") (gates := "not") (table := "10") (goal := "not x") (proof := "(x : Bool) : (!x) = (not x)") (new := "rfl") (play := "a=not; x>a.0; a>out")
:::en
*A wire and a gate.* Drag `not` onto the board, then wire `x` to it and it to the output.
:::

:::de
*Ein Draht und ein Baustein.* Zieh `nicht` aufs Spielfeld, dann verdrahte `x` mit ihm und ihn mit dem
Ausgang.
:::

:::proofen
The statement is your circuit: its output, as a function of `x`, is the target. The tactic `rfl`
proves an equation `a = b` whose two sides become the same after *reducing*. Reducing is computing
by the definitions: Lean replaces a name by its definition, and a function defined by cases by the
case that applies, as soon as it knows the value. `not` is defined by its two cases,
`not false = true` and `not true = false`, so `!true` reduces to `false`, and `!(!true)` to `!false`
and then to `true`. Here nothing has to be computed: `!x` is only another way of writing `not x`.

*Tip.* `rfl`.
:::

:::proofde
Die Aussage ist deine Schaltung: Ihr Ausgang, als Funktion von `x`, ist das Ziel. Die Taktik `rfl`
beweist eine Gleichung `a = b`, deren beide Seiten nach dem *Reduzieren* gleich sind. Reduzieren ist
Rechnen mit den Definitionen: Lean ersetzt einen Namen durch seine Definition, und eine Funktion, die
durch Fälle definiert ist, durch den Fall, der zutrifft, sobald es den Wert kennt. `not` ist durch
seine zwei Fälle definiert, `not false = true` und `not true = false`; also reduziert `!true` zu
`false`, und `!(!true)` zu `!false` und dann zu `true`. Hier muss nichts gerechnet werden: `!x` ist
nur eine andere Schreibweise für `not x`.

*Tipp.* `rfl`.
:::
:::solution
```
rfl
```
:::
::::

::::circuit (inputs := "x") (gates := "not") (table := "01") (goal := "x") (shape := "!(!x)") (start := "a=not; x>a.0") (proof := "(x : Bool) : (!(!x)) = x") (lemma := "Bool.not_not") (new := "cases") (play := "b=not; a>b.0; b>out")
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

::::circuit (inputs := "x y") (gates := "and, or") (table := "0001") (goal := "x && y") (proof := "(x y : Bool) : (x && y) = (x && y)") (play := "a=and; x>a.0; y>a.1; a>out")
:::en
*Both.* The output is `true` only when both inputs are. Four rows now: one for each pair of values.
:::

:::de
*Beide.* Der Ausgang ist nur `true`, wenn beide Eingänge es sind. Jetzt vier Zeilen: eine für jedes
Paar von Werten.
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

::::circuit (inputs := "x") (gates := "not, or") (table := "11") (goal := "true") (proof := "(x : Bool) : (x || !x) = (true)") (new := "<;>") (play := "a=not; b=or; x>a.0; x>b.0; a>b.1; b>out")
:::en
*Always true, without always true.* An output can feed several inputs: wire `x` twice.
:::

:::de
*Immer true, ohne immer true.* Ein Ausgang kann mehrere Eingänge speisen: Verdrahte `x` zweimal.
:::

:::proofen
`||` is defined by cases of its left side: `false || b` reduces to `b`, and `true || b` to `true`.
So `cases x`, then `rfl` in each case. New: `t₁ <;> t₂` runs `t₂` on every goal that `t₁` leaves, in
one line: `cases x <;> rfl`. With several inputs: `cases x <;> cases y <;> rfl`, all rows of the
table at once.

*Tip.* `cases x <;> rfl`.
:::

:::proofde
`||` ist durch Fälle seiner linken Seite definiert: `false || b` reduziert zu `b`, und `true || b` zu
`true`. Also `cases x`, dann `rfl` in jedem Fall. Neu: `t₁ <;> t₂` führt `t₂` auf jedem Ziel aus, das
`t₁` übrig lässt, in einer Zeile: `cases x <;> rfl`. Mit mehreren Eingängen: `cases x <;> cases y <;> rfl`,
alle Zeilen der Tabelle auf einmal.

*Tipp.* `cases x <;> rfl`.
:::
:::solution
```
cases x <;> rfl
```
:::
::::

::::circuit (inputs := "x y") (gates := "and, not") (table := "0111") (goal := "x || y") (proof := "(x y : Bool) : (!(!x && !y)) = (x || y)") (new := "decide") (play := "a=not; b=not; c=and; d=not; x>a.0; y>b.0; a>c.0; b>c.1; c>d.0; d>out")
:::en
*Or, without or.* At least one `true`, with `and` and `not` only. (Not both `false`.)
:::

:::de
*Oder, ohne oder.* Mindestens einmal `true`, nur mit `und` und `nicht`. (Nicht beide `false`.)
:::

:::proofen
This is one of De Morgan's laws: `!(!x && !y) = (x || y)`. By hand: `cases x`, `cases y`, and `rfl`
in each of the four cases, the four rows of the table. The tactic `decide` does that for you: it
reduces a statement about `Bool` until it is `true` or `false`. `decide +revert` first takes the
variables into the statement, here `∀ x y, …`, and so checks every row.

*Tip.* `decide +revert`.
:::

:::proofde
Das ist eine der Regeln von De Morgan: `!(!x && !y) = (x || y)`. Von Hand: `cases x`, `cases y`, und
`rfl` in jedem der vier Fälle, den vier Zeilen der Tafel. Die Taktik `decide` macht das für dich: Sie
reduziert eine Aussage über `Bool`, bis sie `true` oder `false` ist. `decide +revert` nimmt zuerst die
Variablen in die Aussage, hier `∀ x y, …`, und prüft so jede Zeile.

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

::::circuit (inputs := "x y") (gates := "bind") (table := "0001") (goal := "x && y") (proof := "(x y : Bool) : (if x then y else false) = (x && y)") (play := "a=bind; a.T=id; a.F=false; x>a.0; y>a.1; a>out")
:::en
*A gate of your own.* There are four maps `Bool → Bool`: `id`, `not`, always `T`, always `F`. New
gate: `bind`. It has two fields, `T` and `F`, and you put a map into each (drag it in, or tap the
field until it is the one you want). What happens depends on one value only, the one at the input on
the left side: it chooses one of the two fields, `T` or `F` (the blue arrows). The value at the input
on top goes into both fields; the field chosen applies its map to it. In Lean:
`c >>= fun b => if b then f v else g v`. Build `and`: when `x` is `true`, `y` itself; when `x` is
`false`, always `F`. (Show the values row by row: the field not used fades.)
:::

:::de
*Ein eigener Baustein.* Es gibt vier Abbildungen `Bool → Bool`: `id`, `not`, immer `T`, immer `F`.
Neuer Baustein: `bind`. Er hat zwei Felder, `T` und `F`, und in jedes legst du eine
Abbildung (hineinziehen, oder das Feld antippen, bis es die richtige ist). Was passiert, hängt nur von
einem Wert ab, dem am Eingang an der linken Seite: Er wählt eines der beiden Felder, `T` oder `F` (die
blauen Pfeile). Der Wert am Eingang oben geht in beide Felder; das gewählte Feld wendet seine Abbildung
darauf an. In Lean:
`c >>= fun b => if b then f v else g v`. Bau `and`: ist `x` `true`, `y` selbst; ist `x` `false`, immer
`F`. (Zeig die Werte Zeile für Zeile: Das Feld, das nicht benutzt wird, verblasst.)
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

::::circuit (inputs := "x y") (gates := "bind") (table := "0110") (goal := "x ^^ y") (proof := "(x y : Bool) : (if x then !y else y) = (x ^^ y)") (play := "a=bind; a.T=not; a.F=id; x>a.0; y>a.1; a>out")
:::en
*xor, built yourself.* `true` when exactly one input is. With `bind`: for `x = true` one map of `y`,
for `x = false` another. Four maps for each field: sixteen gates with two inputs, all of them.
:::

:::de
*xor, selbst gebaut.* `true`, wenn genau ein Eingang es ist. Mit `bind`: für `x = true` eine
Abbildung von `y`, für `x = false` eine andere. Vier Abbildungen für jedes Feld: sechzehn Bausteine mit
zwei Eingängen, alle.
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

::::circuit (inputs := "x y") (gates := "bind") (table := "1101") (goal := "!x || y") (proof := "(x y : Bool) : (if x then y else true) = (!x || y)") (play := "a=bind; a.T=id; a.F=true; x>a.0; y>a.1; a>out")
:::en
*If x, then y.* The implication: `false` only when `x` is `true` and `y` is `false`. In Lean
`!x || y`.
:::

:::de
*Wenn x, dann y.* Die Implikation: `false` nur, wenn `x` `true` ist und `y` `false`. In Lean
`!x || y`.
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

::::circuit (inputs := "true") (gates := "f") (table := "1") (shape := "f (f true)") (every := "id true") (proof := "(f : Bool → Bool) (h : f true = true) : f (f true) = true") (new := "rw") (play := "a=f; b=f; a.0=id; true>a.0; a>b.0; b>out")
:::en
*The same map twice.* New gate: `f`, an unknown map. It has one field for one of the four maps, and
every `f` on the board has the same one. The input is `true` itself. Build `f (f true)`: the output is
to be `true` again. In Lean `f` is any map with `f true = true`. Which of the four are
these? Try each of them in `f`: the board ticks off the ones that count.
:::

:::de
*Zweimal dieselbe Abbildung.* Neuer Baustein: `f`, eine unbekannte Abbildung. Er hat ein Feld für
eine der vier Abbildungen, und jedes `f` auf dem Spielfeld hat dieselbe. Der Eingang ist `true` selbst.
Bau `f (f true)`: Der Ausgang soll wieder `true` sein. In Lean ist `f` irgendeine Abbildung mit
`f true = true`. Welche der vier sind das? Probier jede in `f` aus: Das Spielfeld hakt die ab, die
zählen.
:::

:::proofen
A map `f` that sends `true` to `true`, the hypothesis `h : f true = true`, does so twice. Here `rfl`
cannot help: nothing is known of `f` but `h`. `rw [h]` rewrites with the hypothesis: `f true` becomes
`true`, wherever it stands in the goal.

*Tip.* `rw [h, h]`.
:::

:::proofde
Eine Abbildung `f`, die `true` nach `true` schickt, die Annahme `h : f true = true`, tut das auch
zweimal. Hier hilft `rfl` nicht: Von `f` ist nichts bekannt außer `h`. `rw [h]` schreibt mit der
Annahme um: `f true` wird `true`, wo immer es im Ziel steht.

*Tipp.* `rw [h, h]`.
:::
:::solution
```
rw [h, h]
```
:::
::::

::::circuit (inputs := "b") (gates := "f") (table := "f") (shape := "f (f (f b))") (every := "id not true false") (proof := "(f : Bool → Bool) (b : Bool) : f (f (f b)) = f b") (play := "a=f; c=f; d=f; b>a.0; a>c.0; c>d.0; d>out")
:::en
*Three times is once.* Build `f (f (f b))`. The target is `f` itself, once: for every map in `f`,
three times is to be the same as once. Check it for each of the four maps.
:::

:::de
*Dreimal ist einmal.* Bau `f (f (f b))`. Das Ziel ist `f` selbst, einmal: Für jede Abbildung in `f`
soll dreimal dasselbe sein wie einmal. Prüf es für jede der vier Abbildungen.
:::

:::proofen
No rule says what `f` does. But there are only four maps `Bool → Bool`, the four you tried, and with
the two values of `b` these are eight cases. `decide +revert` checks them all, as the board did. With
coins this no longer works: a coin `coin p` is a different distribution for every number `p` between
0 and 1, infinitely many cases. There, the rules do the work.

*Tip.* `decide +revert`.
:::

:::proofde
Keine Regel sagt, was `f` tut. Aber es gibt nur vier Abbildungen `Bool → Bool`, die vier, die du
ausprobiert hast, und mit den zwei Werten von `b` sind das acht Fälle. `decide +revert` prüft sie
alle, wie das Spielfeld. Mit Münzen geht das nicht mehr: Eine Münze `coin p` ist für jede Zahl `p`
zwischen 0 und 1 eine andere Verteilung, unendlich viele Fälle. Dort machen die Regeln die Arbeit.

*Tipp.* `decide +revert`.
:::
:::solution
```
decide +revert
```
:::
::::

::::circuit (inputs := "x") (gates := "toNat, not") (table := "nat 10") (goal := "1 - x.toNat") (proof := "(x : Bool) : ((!x).toNat) = (1 - x.toNat)") (play := "a=not; b=toNat; x>a.0; a>b.0; b>out")
:::en
*A number.* New gate: `toNat` makes a coin a number, `false` is `0` and `true` is `1`. Its output is
blue: a wire of numbers. The target is now a number in every row: `1` when `x` is `false`, `0` when
it is `true`.
:::

:::de
*Eine Zahl.* Neuer Baustein: `toNat` macht aus einer Münze eine Zahl, `false` ist `0` und `true` ist
`1`. Sein Ausgang ist blau: ein Draht mit Zahlen. Das Ziel ist jetzt in jeder Zeile eine Zahl: `1`,
wenn `x` `false` ist, `0`, wenn es `true` ist.
:::

:::proofen
*Tip.* `decide +revert`: the numbers are compared as well.
:::

:::proofde
*Tipp.* `decide +revert`: auch Zahlen werden verglichen.
:::
:::solution
```
decide +revert
```
:::
::::

::::circuit (inputs := "x y") (gates := "toNat, plus, and, or, not") (table := "nat 0112") (goal := "x.toNat + y.toNat") (proof := "(x y : Bool) : (x.toNat + y.toNat) = (x.toNat + y.toNat)") (play := "a=toNat; b=toNat; c=plus; x>a.0; y>b.0; a>c.0; b>c.1; c>out")
:::en
*Count.* New gate: `plus` adds two numbers. The target counts how many of `x`, `y` are `true`:
`0`, `1` or `2`. A coin does not fit into `plus`: first `toNat`.
:::

:::de
*Zählen.* Neuer Baustein: `plus` addiert zwei Zahlen. Das Ziel zählt, wie viele von `x`, `y` `true`
sind: `0`, `1` oder `2`. Eine Münze passt nicht in `plus`: erst `toNat`.
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
