import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Circuits" =>

%%%
htmlSplit := .never
number := false
%%%

::::hint (anchor := "world")
:::en
This introductory world teaches you about Boolean variables: `true` and `false`.
:::

:::de
Diese Einführungswelt bringt dir Boolesche Variablen bei: `true` und `false`.
:::
::::

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

:::::circuit (height := "300") (inputs := "x") (gates := "") (table := "01") (goal := "x") (shape := "x") (proof := "(x : Bool) : x = x") (new := "rfl") (play := "x>out") (uses := "-")
:::en
*A wire.* The output is to be the input itself. Wire `x` to the output: tap `x`, then the output.
:::

:::de
*Ein Draht.* Der Ausgang soll der Eingang selbst sein. Verdrahte `x` mit dem Ausgang: Tippe `x` an,
dann den Ausgang.
:::

::::hint (anchor := "output")
:::en
This is the game piece. `F` is for `false`, `T` is for `true`, `?` is for either of them. Connect
the input `x` to the game piece such that *Target* and *Output* match.
:::

:::de
Das ist der Spielstein. `F` steht für `false`, `T` für `true`, `?` für eins von beiden. Verbinde
den Eingang `x` so mit dem Spielstein, dass *Ziel* und *Ausgang* übereinstimmen.
:::
::::

:::proofen
Let us start easy and translate the last level to Lean. The board reads: the output, `x`, is the
target, `x`. In Lean, `example (x : Bool) : x = x` says *for every `x` of type `Bool`, `x = x`*.
Before the colon stand the variables (and later the hypotheses), after it what is claimed. Below the
statement Lean shows the *goal*: the variables on top, and after `⊢` what is still to be shown. A
*tactic*, one line, changes the goal, until nothing is left.

`rfl` is a tactic that proves an equation whose two sides are the same (*reflexivity*: everything is
equal to itself).

*Tip.* `rfl`.
:::

:::proofde
Fangen wir leicht an und übersetzen das letzte Level nach Lean. Das Spielfeld sagt: Der Ausgang, `x`,
ist das Ziel, `x`. In Lean sagt `example (x : Bool) : x = x`: *für jedes `x` vom Typ `Bool` ist
`x = x`*. Vor dem Doppelpunkt stehen die Variablen (und später die Annahmen), danach das, was
behauptet wird. Unter der Aussage zeigt Lean das *Ziel*: oben die Variablen, und nach `⊢` das, was
noch zu zeigen ist. Eine *Taktik*, eine Zeile, ändert das Ziel, bis nichts mehr übrig ist.

`rfl` ist eine Taktik, die eine Gleichung beweist, deren beide Seiten gleich sind (*Reflexivität*:
alles ist sich selbst gleich).

*Tipp.* `rfl`.
:::
:::solution
```
rfl
```
:::
:::::

:::::circuit (height := "400") (inputs := "x") (gates := "not") (table := "10") (goal := "!x") (shape := "!x") (proof := ": (!true) = false") (lemma := "Bool.not_true") (play := "a=not; x>a.0; a>out") (uses := "-")
:::en
*Not.* The output is to be the other value: `false` for `true`, and `true` for `false`. Drag `not`
onto the board, then wire `x` to it and it to the output.
:::

:::de
*Nicht.* Der Ausgang soll der andere Wert sein: `false` für `true`, und `true` für `false`. Zieh
`nicht` aufs Spielfeld, dann verdrahte `x` mit ihm und ihn mit dem Ausgang.
:::

::::hint (anchor := "move:not")
:::en
Click on a game piece or drag it in order to use it!
:::

:::de
Tippe einen Spielstein an oder zieh ihn aufs Spielfeld, um ihn zu benutzen!
:::
::::

::::hint (anchor := "item:rfl")
:::en
*Equal* means here: *equal after reduction*. `not` (abbreviated `!` here) is defined as the function
`fun | true => false | false => true`.
:::

:::de
*Gleich* heißt hier: *gleich nach Reduktion*. `not` (hier abgekürzt `!`) ist definiert als die
Funktion `fun | true => false | false => true`.
:::
::::

:::proofen
In Lean, one column at a time: here the column `x = true`, the statement `(!true) = false` (the
column `x = false` is the next level). Now the two sides are not the same as they stand: `!true` on the left, `false` on the right. But
`rfl` also *reduces*: it computes with the definitions. `not` is defined by its two cases,

`fun | true => false | false => true`

(a function given by cases: `true` goes to `false`, `false` to `true`). Here Lean knows the value,
`true`, so it takes that case: `!true` reduces to `false`. Then both sides are the same.

*Tip.* `rfl`.
:::

:::proofde
In Lean eine Spalte nach der anderen: hier die Spalte `x = true`, die Aussage `(!true) = false` (die
Spalte `x = false` ist das nächste Level). Jetzt sind die beiden Seiten nicht so, wie sie dastehen, gleich: links `!true`, rechts `false`. Aber
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
:::::

::::leanonly (proof := ": (!false) = true") (lemma := "Bool.not_false") (context := "Lean/WorldBool.lean") (group := "bool") (uses := "-")
:::hint (anchor := "none")
:::

:::en
*Not false.* The other column of `not`, in Lean only: the level before proved `(!true) = false`,
the rule `Bool.not_true`.
:::

:::de
*Nicht false.* Die andere Spalte von `not`, nur in Lean: Das Level davor hat `(!true) = false`
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

:::::circuit (height := "500") (inputs := "x") (gates := "not") (table := "01") (goal := "x") (shape := "!(!x)") (start := "a=not; x>a.0") (proof := "(x : Bool) : (!(!x)) = x") (lemma := "Bool.not_not") (new := "cases") (play := "b=not; a>b.0; b>out") (uses := "-")
:::en
*Flipped twice.* One `not` is already on the board and stays there. Add a second one, so that the output is the input again.
:::

:::de
*Zweimal umgedreht.* Ein `nicht` liegt schon auf dem Spielfeld und bleibt dort. Füge ein zweites hinzu, sodass der Ausgang wieder der Eingang ist.
:::

::::hint (anchor := "item:cases")
:::en
`rfl` can only unfold definitions if no variables (`x` here) are involved. `cases x` makes Lean
distinguish the two cases, `x = false` and `x = true`.
:::

:::de
`rfl` kann Definitionen nur auflösen, wenn keine Variablen (hier `x`) beteiligt sind. `cases x` lässt
Lean die zwei Fälle unterscheiden, `x = false` und `x = true`.
:::
::::

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
:::::

::::circuit (height := "500") (inputs := "x") (gates := "not, or") (table := "11") (goal := "true") (proof := "(x : Bool) : (x || ⟦!x ‖ x, !x, false⟧) = true") (play := "a=not; b=or; x>a.0; x>b.0; a>b.1; b>out") (uses := "-")
:::en
*Always true, without always true.* An output can feed several inputs: wire `x` twice.
:::

:::de
*Immer true, ohne immer true.* Ein Ausgang kann mehrere Eingänge speisen: Verdrahte `x` zweimal.
:::

:::proofen
First the statement: your circuit is `x || ▢`, and it is to be `true` for every `x`. What goes into
the gap? Then the proof: `||` is defined by cases of its left side, `false || b` reduces to `b`, and
`true || b` to `true`. So `cases x`, then `rfl` in each case.

*Tip.* `!x`; then `cases x`, `rfl`, `rfl`.
:::

:::proofde
Zuerst die Aussage: Deine Schaltung ist `x || ▢`, und sie soll für jedes `x` `true` sein. Was gehört
in die Lücke? Dann der Beweis: `||` ist durch Fälle seiner linken Seite definiert, `false || b`
reduziert zu `b`, und `true || b` zu `true`. Also `cases x`, dann `rfl` in jedem Fall.

*Tipp.* `!x`; dann `cases x`, `rfl`, `rfl`.
:::
:::solution
```
cases x
rfl
rfl
```
:::
::::

::::leanonly (proof := "(a b : Bool) : (bif true then a else b) = a") (lemma := "Bool.cond_true") (context := "Lean/WorldBool.lean") (group := "bool") (uses := "-")
:::en
*bif with true.* `bif c then a else b` is `a` when `c` is `true`, and `b` when it is `false`: an
if-then-else for a `Bool`. The boss needs it, and later the coins: where the mass of a move goes.
:::

:::de
*bif mit true.* `bif c then a else b` ist `a`, wenn `c` gleich `true` ist, und `b`, wenn es `false`
ist: ein Wenn-dann-sonst für ein `Bool`. Der Endgegner braucht es, und später die Münzen: wohin die
Masse eines Zuges geht.
:::

:::proofen
`bif` is defined by the two cases of `c`; here `c` is `true`.

*Tip.* `rfl`.
:::

:::proofde
`bif` ist durch die zwei Fälle von `c` definiert; hier ist `c` gleich `true`.

*Tipp.* `rfl`.
:::
:::solution
```
rfl
```
:::
::::

::::leanonly (proof := "(a b : Bool) : (bif false then a else b) = b") (lemma := "Bool.cond_false") (context := "Lean/WorldBool.lean") (group := "bool") (uses := "-")
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

::::circuit (inputs := "x y") (gates := "and, or, not") (table := "0110") (goal := "x ^^ y") (proof := "(x y : Bool) : ((x || y) && !(x && y)) = (bif x then (bif y then ⟦false ‖ true, false⟧ else ⟦true ‖ true, false⟧) else (bif y then ⟦true ‖ true, false⟧ else ⟦false ‖ true, false⟧))") (play := "a=or; b=and; c=not; d=and; x>a.0; y>a.1; x>b.0; y>b.1; b>c.0; a>d.0; c>d.1; d>out") (new := "<;>") (uses := "-")
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
four rows. New: `t₁ <;> t₂` runs `t₂` on every goal that `t₁` leaves; so all in one line.

*Tip.* `cases x <;> cases y <;> rfl`.
:::

:::proofde
Die Tafel hat jetzt vier Zeilen, eine für jedes Paar von Werten: erst entscheidet `x`, dann `y`, ein
`bif` in jedem Zweig eines `bif`. `cases x` macht zwei Ziele; in jedem macht `cases y` zwei weitere:
vier Ziele, die vier Zeilen. Neu: `t₁ <;> t₂` führt `t₂` auf jedem Ziel aus, das `t₁` übrig lässt; so
alles in einer Zeile.

*Tipp.* `cases x <;> cases y <;> rfl`.
:::
:::solution
```
cases x <;> cases y <;> rfl
```
:::
::::
