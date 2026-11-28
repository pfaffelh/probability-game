import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Bool" =>

%%%
htmlSplit := .never
file := "Circuits"
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

:::::circuit (height := "300") (inputs := "x") (gates := "") (table := "01") (goal := "x") (shape := "x") (proof := "(x : Bool) : x = x") (new := "rfl") (play := "x>out") (uses := "rfl")
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

::::hint (anchor := "lean")
:::en
Let us prove this in Lean!
:::

:::de
Beweisen wir das in Lean!
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
:::

:::proofde
Fangen wir leicht an und übersetzen das letzte Level nach Lean. Das Spielfeld sagt: Der Ausgang, `x`,
ist das Ziel, `x`. In Lean sagt `example (x : Bool) : x = x`: *für jedes `x` vom Typ `Bool` ist
`x = x`*. Vor dem Doppelpunkt stehen die Variablen (und später die Annahmen), danach das, was
behauptet wird. Unter der Aussage zeigt Lean das *Ziel*: oben die Variablen, und nach `⊢` das, was
noch zu zeigen ist. Eine *Taktik*, eine Zeile, ändert das Ziel, bis nichts mehr übrig ist.

`rfl` ist eine Taktik, die eine Gleichung beweist, deren beide Seiten gleich sind (*Reflexivität*:
alles ist sich selbst gleich).
:::
:::solution
```
rfl
```
:::
:::::

:::::circuit (height := "400") (inputs := "x") (gates := "not") (table := "10") (goal := "!x") (shape := "!x") (proof := ": (!true) = false") (lemma := "Bool.not_true") (play := "a=not; x>a.0; a>out") (uses := "rfl")
::::hint (anchor := "statement")
:::en
`@[simp]` marks a lemma for the simplifier `simp`, which you meet later: it then uses the lemma by itself.
:::

:::de
`@[simp]` markiert ein Lemma für den Simplifier `simp`, den du später kennenlernst: Er benutzt das Lemma dann von selbst.
:::
::::

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
:::

:::proofde
In Lean eine Spalte nach der anderen: hier die Spalte `x = true`, die Aussage `(!true) = false` (die
Spalte `x = false` ist das nächste Level). Jetzt sind die beiden Seiten nicht so, wie sie dastehen, gleich: links `!true`, rechts `false`. Aber
`rfl` *reduziert* auch: Es rechnet mit den Definitionen. `not` ist durch seine zwei Fälle definiert,

`fun | true => false | false => true`

(eine Funktion, durch Fälle gegeben: `true` geht nach `false`, `false` nach `true`). Hier kennt Lean
den Wert, `true`, also nimmt es diesen Fall: `!true` reduziert zu `false`. Danach sind beide Seiten
gleich.
:::
:::solution
```
rfl
```
:::
:::::

::::leanonly (proof := ": (!false) = true") (lemma := "Bool.not_false") (context := "Lean/WorldBool.lean") (group := "bool") (uses := "rfl")
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
:::

:::proofde
`not` ist durch seine zwei Fälle definiert, und hier kennt Lean den Wert: `!false` reduziert zu
`true`.
:::
:::solution
```
rfl
```
:::
::::

:::::leanonly (proof := ": (!(!true)) = true") (context := "Lean/WorldBool.lean") (group := "bool") (new := "rw") (uses := "Bool.not_true, Bool.not_false, rw, -rfl")
::::hint (anchor := "item:rw")
:::en
`rw [h]` rewrites the goal with a theorem `h : a = b`: every `a` becomes `b`.
:::

:::de
`rw [h]` schreibt das Ziel mit einem Satz `h : a = b` um: Jedes `a` wird zu `b`.
:::
::::

:::en
*Back again.* Twice `not` on `true`, with the two theorems you proved.
:::

:::de
*Wieder zurück.* Zweimal `not` auf `true`, mit den zwei Sätzen, die du bewiesen hast.
:::

:::proofen
`rfl` would compute this as well. Here with your theorems: `rw [h]` *rewrites* the goal with a
theorem `h : a = b`, it replaces the left side `a` by the right side `b`. When both sides of the
goal are then the same, `rw` closes it.
:::

:::proofde
`rfl` würde auch das ausrechnen. Hier mit deinen Sätzen: `rw [h]` *schreibt* das Ziel mit einem Satz
`h : a = b` *um*, es ersetzt die linke Seite `a` durch die rechte `b`. Sind danach beide Seiten des
Ziels gleich, schließt `rw` es.
:::
:::solution
```
rw [Bool.not_true, Bool.not_false]
```
:::
:::::

:::::circuit (height := "500") (inputs := "x") (gates := "not") (table := "01") (goal := "x") (shape := "!(!x)") (start := "a=not; x>a.0") (proof := "(x : Bool) : (!(!x)) = x") (lemma := "Bool.not_not") (new := "cases") (play := "b=not; a>b.0; b>out") (uses := "Bool.not_false, Bool.not_true, cases, rfl, rw")
:::hint (anchor := "none")
:::

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

::::hint (anchor := "after:cases")
:::en
`cases x` has made two new goals out of one: in the first `x` is `false`, in the second `true`. Prove
them one after the other.
:::

:::de
`cases x` hat aus einem Ziel zwei neue gemacht: Im ersten ist `x` gleich `false`, im zweiten `true`.
Beweise sie nacheinander.
:::
::::

:::proofen
`!(!x) = x` for every `x`. Now `rfl` does not help: `not` is defined by its cases, and Lean cannot
reduce `!x` as long as it does not know `x`. The tactic `cases x` splits into the cases `false` and
`true`, two goals one after the other, as the two rows of the table. Your result becomes the lemma
`Bool.not_not`, as it is called in Lean.
:::

:::proofde
`!(!x) = x` für jedes `x`. Jetzt hilft `rfl` nicht: `not` ist durch seine Fälle definiert, und Lean
kann `!x` nicht reduzieren, solange es `x` nicht kennt. Die Taktik `cases x` teilt in die Fälle
`false` und `true`, zwei Ziele nacheinander, wie die zwei Zeilen der Tafel. Dein Ergebnis wird das
Lemma `Bool.not_not`, wie es in Lean heißt.
:::
:::solution
```
cases x
rfl
rfl
```
:::
:::solution
```
cases x
rw [Bool.not_false, Bool.not_true]
rw [Bool.not_true, Bool.not_false]
```
:::
:::solution
```
cases x
rfl
rw [Bool.not_true, Bool.not_false]
```
:::
:::solution
```
cases x
rw [Bool.not_false]
rfl
rw [Bool.not_true]
rfl
```
:::
:::::

:::::circuit (height := "500") (inputs := "x") (gates := "not, or, and") (table := "11") (goal := "true") (proof := "(x : Bool) : (x || !x) = true") (lemma := "Bool.or_not_self") (play := "a=not; b=or; x>a.0; x>b.0; a>b.1; b>out") (uses := "Bool.not_false, Bool.not_true, cases, rfl, rw")
:::hint (anchor := "none")
:::

:::en
*Always true, without always true.* An output can feed several inputs: wire `x` twice.
:::

:::de
*Immer true, ohne immer true.* Ein Ausgang kann mehrere Eingänge speisen: Verdrahte `x` zweimal.
:::

:::proofen
`||` is defined by cases of its left side: `false || b` reduces to `b`, and `true || b` to `true`.
Your result becomes the lemma `Bool.or_not_self`.
:::

:::proofde
`||` ist durch Fälle seiner linken Seite definiert: `false || b` reduziert zu `b`, und `true || b`
zu `true`. Dein Ergebnis wird das Lemma `Bool.or_not_self`.
:::
:::solution
```
cases x
rfl
rfl
```
:::
:::solution
```
cases x
rw [Bool.not_false]
rfl
rw [Bool.not_true]
rfl
```
:::
:::solution
```
cases x
rw [Bool.not_false]
rfl
rfl
```
:::
:::solution
```
cases x
rfl
rw [Bool.not_true]
rfl
```
:::
:::::

::::leanonly (proof := "(a b : Bool) : (bif true then a else b) = ⟦a ‖ a, b, true, false⟧") (lemma := "Bool.cond_true") (context := "Lean/WorldBool.lean") (group := "bool") (uses := "cases, rfl")
:::en
*bif with true.* `bif` is Lean's *Boolean if*: `bif c then a else b` is if-then-else with a
condition `c : Bool`.
:::

:::de
*bif mit true.* `bif` ist Leans *Boolean if*: `bif c then a else b` ist Wenn-dann-sonst mit einer
Bedingung `c : Bool`.
:::

:::solution
```
rfl
```
:::
:::solution
```
cases a
rfl
rfl
```
:::
::::

:::::circuit (height := "500") (inputs := "x") (gates := "not, or, and") (table := "01") (goal := "x") (proof := "(x : Bool) : (x && x) = x") (lemma := "Bool.and_self") (play := "a=and; x>a.0; x>a.1; a>out") (new := "<;>") (uses := "<;>, cases, rfl")
::::hint (anchor := "item:<;>")
:::en
`t₁ <;> t₂` runs `t₂` on every goal that `t₁` leaves.
:::

:::de
`t₁ <;> t₂` führt `t₂` auf jedem Ziel aus, das `t₁` übrig lässt.
:::
::::

:::en
*Twice the same.* `x` and `x`: wire `x` into both inputs of an `and`.
:::

:::de
*Zweimal dasselbe.* `x` und `x`: Verdrahte `x` in beide Eingänge eines `und`.
:::

:::proofen
`&&` is defined by cases of its left side, as `||`. Your result becomes the lemma `Bool.and_self`.
:::

:::proofde
`&&` ist durch Fälle seiner linken Seite definiert, wie `||`. Dein Ergebnis wird das Lemma
`Bool.and_self`.
:::
:::solution
```
cases x <;> rfl
```
:::
:::solution
```
cases x
rfl
rfl
```
:::
:::::

:::::circuit (height := "500") (inputs := "x") (gates := "not, or, and") (table := "00") (goal := "false") (proof := "(x : Bool) : (x && !x) = false") (lemma := "Bool.and_not_self") (play := "a=not; b=and; x>a.0; x>b.0; a>b.1; b>out") (uses := "Bool.not_false, Bool.not_true, <;>, cases, rfl, rw")
::::hint (anchor := "none")
::::

:::en
*Never both.* Always `false`, without always `false`: `x` and its opposite.
:::

:::de
*Nie beides.* Immer `false`, ohne immer `false`: `x` und sein Gegenteil.
:::

:::proofen
The counterpart of *Always true, without always true*, with `&&` instead of `||`. Your result becomes
the lemma `Bool.and_not_self`.
:::

:::proofde
Das Gegenstück zu *Immer true, ohne immer true*, mit `&&` statt `||`. Dein Ergebnis wird das Lemma
`Bool.and_not_self`.
:::
:::solution
```
cases x <;> rfl
```
:::
:::solution
```
cases x
rfl
rfl
```
:::
:::solution
```
cases x
rw [Bool.not_false]
rfl
rw [Bool.not_true]
rfl
```
:::
:::solution
```
cases x
rfl
rw [Bool.not_true]
rfl
```
:::
:::::

::::leanonly (proof := "(a b : Bool) : (bif false then a else b) = ⟦b ‖ a, b, true, false⟧") (lemma := "Bool.cond_false") (context := "Lean/WorldBool.lean") (group := "bool") (uses := "<;>, cases, rfl")
:::hint (anchor := "none")
:::

:::en
*bif with false.* The other case: the second.
:::

:::de
*bif mit false.* Der andere Fall: das Zweite.
:::
:::solution
```
rfl
```
:::
:::solution
```
cases b
rfl
rfl
```
:::
:::solution
```
cases b <;> rfl
```
:::
::::

::::leanonly (proof := "(x : Bool) : (true && x) = ⟦x ‖ x, true, false⟧") (lemma := "Bool.true_and") (context := "Lean/WorldBool.lean") (group := "bool") (uses := "<;>, cases, rfl")
:::hint (anchor := "none")
:::

:::en
*true and x.* The table of `&&`, as a rule: `&&` looks at its left side first. If it is `true`, the right side decides.
:::

:::de
*true und x.* Die Tabelle von `&&`, als Regel: `&&` schaut zuerst auf seine linke Seite. Ist sie `true`, entscheidet die rechte.
:::
:::solution
```
rfl
```
:::
:::solution
```
cases x <;> rfl
```
:::
:::solution
```
cases x
rfl
rfl
```
:::
::::

::::leanonly (proof := "(x : Bool) : (false && x) = ⟦false ‖ false, true, x⟧") (lemma := "Bool.false_and") (context := "Lean/WorldBool.lean") (group := "bool") (uses := "<;>, cases, rfl")
:::hint (anchor := "none")
:::

:::en
*false and x.* If the left side is `false`, the right side does not matter.
:::

:::de
*false und x.* Ist die linke Seite `false`, spielt die rechte keine Rolle.
:::
:::solution
```
rfl
```
:::
:::solution
```
cases x <;> rfl
```
:::
:::solution
```
cases x
rfl
rfl
```
:::
::::

::::leanonly (proof := "(x : Bool) : (true || x) = ⟦true ‖ true, false, x⟧") (lemma := "Bool.true_or") (context := "Lean/WorldBool.lean") (group := "bool") (uses := "<;>, cases, rfl")
:::hint (anchor := "none")
:::

:::en
*true or x.* The table of `||`: with `true` on the left, the right side does not matter.
:::

:::de
*true oder x.* Die Tabelle von `||`: Mit `true` links spielt die rechte Seite keine Rolle.
:::
:::solution
```
rfl
```
:::
:::solution
```
cases x <;> rfl
```
:::
:::solution
```
cases x
rfl
rfl
```
:::
::::

::::leanonly (proof := "(x : Bool) : (false || x) = ⟦x ‖ x, true, false⟧") (lemma := "Bool.false_or") (context := "Lean/WorldBool.lean") (group := "bool") (uses := "<;>, cases, rfl")
:::hint (anchor := "none")
:::

:::en
*false or x.* With `false` on the left, the right side decides. With these four rules you can compute `&&` and `||` step by step.
:::

:::de
*false oder x.* Mit `false` links entscheidet die rechte Seite. Mit diesen vier Regeln rechnest du `&&` und `||` Schritt für Schritt aus.
:::
:::solution
```
rfl
```
:::
:::solution
```
cases x <;> rfl
```
:::
:::solution
```
cases x
rfl
rfl
```
:::
::::

::::leanonly (proof := "(c a : Bool) : (bif c then a else a) = ⟦a ‖ a, c, true, false⟧") (lemma := "Bool.cond_self") (context := "Lean/WorldBool.lean") (group := "bool") (uses := "Bool.cond_false, Bool.cond_true, cases, rw, -rfl")
:::hint (anchor := "none")
:::

:::en
*bif with the same twice.* When both branches are the same, the condition does not matter.
:::

:::de
*bif mit zweimal demselben.* Sind beide Zweige gleich, ist die Bedingung egal.
:::
:::solution
```
cases c
rw [Bool.cond_false]
rw [Bool.cond_true]
```
:::
::::

::::leanonly (proof := "(b : Bool) : (b == b) = ⟦true ‖ true, false, b⟧") (lemma := "beq_self_eq_true") (context := "Lean/WorldBool.lean") (group := "bool") (uses := "<;>, cases, rfl")
:::en
*Tested against itself.* `a == b` asks whether `a` and `b` are equal, and answers `true` or `false`.
:::

:::de
*Mit sich selbst verglichen.* `a == b` fragt, ob `a` und `b` gleich sind, und antwortet `true` oder `false`.
:::

:::proofen
`==` on `Bool` is defined by cases, as `&&` and `||`. Your result becomes the lemma `beq_self_eq_true`.
:::

:::proofde
`==` ist auf `Bool` durch Fälle definiert, wie `&&` und `||`. Dein Ergebnis wird das Lemma
`beq_self_eq_true`.
:::
:::solution
```
cases b <;> rfl
```
:::
:::solution
```
cases b
rfl
rfl
```
:::
::::

::::leanonly (proof := "(c : Bool) : (c == true) = ⟦c ‖ c, !c, true⟧") (lemma := "beq_true") (context := "Lean/WorldBool.lean") (group := "bool") (uses := "beq_self_eq_true, <;>, cases, rfl, rw")
:::en
*Equal to true.* `c == b` is a test, itself a `Bool`. Testing `c == true` gives back `c` itself.
:::

:::de
*Gleich true.* `c == b` ist ein Test, selbst ein `Bool`. Der Test `c == true` gibt `c` selbst zurück.
:::

:::proofen
Two cases: `c` is `true` or `false`, and in each Lean computes both sides.
:::

:::proofde
Zwei Fälle: `c` ist `true` oder `false`, und in jedem rechnet Lean beide Seiten aus.
:::
:::solution
```
cases c <;> rfl
```
:::
:::solution
```
cases c
rfl
rfl
```
:::
:::solution
```
cases c
rfl
rw [beq_self_eq_true]
```
:::
::::

::::leanonly (proof := "(b : Bool) : (true == b) = ⟦b ‖ b, !b, true⟧") (lemma := "Bool.true_beq") (context := "Lean/WorldBool.lean") (group := "bool") (uses := "beq_self_eq_true, beq_true, <;>, cases, rfl, rw")
:::en
*true tested.* Now `true` stands in front: `true == b` is `b`.
:::

:::de
*true getestet.* Jetzt steht `true` vorne: `true == b` ist `b`.
:::
:::solution
```
cases b <;> rfl
```
:::
:::solution
```
cases b
rfl
rw [beq_self_eq_true]
```
:::
:::solution
```
cases b
rfl
rw [beq_true]
```
:::
::::

::::leanonly (proof := "(b : Bool) : (false == b) = ⟦!b ‖ !b, b, false⟧") (lemma := "Bool.false_beq") (context := "Lean/WorldBool.lean") (group := "bool") (uses := "beq_self_eq_true, Bool.not_false, Bool.not_true, <;>, cases, rfl, rw")
:::en
*false tested.* With `false` in front, the test turns `b` round: `false == b` is `!b`.
:::

:::de
*false getestet.* Mit `false` vorne dreht der Test `b` um: `false == b` ist `!b`.
:::
:::solution
```
cases b <;> rfl
```
:::
:::solution
```
cases b
rw [beq_self_eq_true, Bool.not_false]
rfl
```
:::
::::

::::leanonly (proof := "(x y : ℕ) : ∑ a, (bif a then x else y) = x + y") (new := "Fintype.sum_bool") (context := "Lean/WorldBool.lean") (group := "bool") (uses := "Fintype.sum_bool, Bool.cond_true, Bool.cond_false, rw, -rfl")
:::en
*A sum over Bool.* `∑ a, g a` is the sum of `g a` over all points `a` of a finite type; over `Bool`
there are two, and the rule (from Mathlib) is

`Fintype.sum_bool : ∑ a, g a = g true + g false`.

Later the masses of a distribution are added up this way.
:::

:::de
*Eine Summe über Bool.* `∑ a, g a` ist die Summe der `g a` über alle Punkte `a` eines endlichen Typs;
über `Bool` sind es zwei, und die Regel (aus Mathlib) ist

`Fintype.sum_bool : ∑ a, g a = g true + g false`.

Später werden so die Massen einer Verteilung addiert.
:::

:::proofen
Here `g a` is `bif a then x else y`.
:::

:::proofde
Hier ist `g a` gleich `bif a then x else y`.
:::
:::solution
```
rw [Fintype.sum_bool, Bool.cond_true, Bool.cond_false]
```
:::
:::solution
```
rw [Fintype.sum_bool, Bool.cond_false, Bool.cond_true]
```
:::
::::

::::leanonly (proof := "(x y : ℕ) : ∑' a, (bif a then x else y) = y + x") (new := "tsum_bool") (context := "Lean/WorldBool.lean") (group := "bool") (uses := "tsum_bool, Bool.cond_false, Bool.cond_true, rw, -rfl")
:::en
*A sum over all points.* `∑' a, g a`, with a prime, is the sum over all points of any type, also of
infinitely many (in Mathlib `tsum`). Over `Bool` it is the sum of two terms, `false` first:

`tsum_bool : ∑' a, g a = g false + g true`.
:::

:::de
*Eine Summe über alle Punkte.* `∑' a, g a`, mit Strich, ist die Summe über alle Punkte eines
beliebigen Typs, auch über unendlich viele (in Mathlib `tsum`). Über `Bool` ist es die Summe zweier
Summanden, `false` zuerst:

`tsum_bool : ∑' a, g a = g false + g true`.
:::
:::solution
```
rw [tsum_bool, Bool.cond_false, Bool.cond_true]
```
:::
:::solution
```
rw [tsum_bool, Bool.cond_true, Bool.cond_false]
```
:::
::::

::::leanonly (proof := "(f : Bool → Bool) : (fun _ : Bool => true) ∘ f = fun _ => ⟦true ‖ true, false, f true⟧") (context := "Lean/WorldBool.lean") (group := "bool") (uses := "rfl")
:::en
*Always true, after anything.* `g ∘ f` is `g` after `f`: `(g ∘ f) x = g (f x)`. After *always true*
it does not matter what `f` did before.
:::

:::de
*Immer true, nach allem.* `g ∘ f` ist `g` nach `f`: `(g ∘ f) x = g (f x)`. Nach *immer true* ist
egal, was `f` vorher getan hat.
:::

:::proofen
Both sides are the same map: Lean sees it by computing, `rfl`.
:::

:::proofde
Beide Seiten sind dieselbe Abbildung: Lean sieht es durch Rechnen, `rfl`.
:::
:::solution
```
rfl
```
:::
::::

::::leanonly (proof := "(f : Bool → Bool) : f ∘ (fun _ : Bool => true) = fun _ => ⟦f true ‖ true, f true, f false⟧") (context := "Lean/WorldBool.lean") (group := "bool") (uses := "rfl")
:::en
*The other way round: anything after always true.* First *always true*, then `f`: the result is
always the same, `f true`.
:::

:::de
*Andersherum: alles nach immer true.* Erst *immer true*, dann `f`: Das Ergebnis ist immer dasselbe,
`f true`.
:::

:::proofen
Again by computing, `rfl`.
:::

:::proofde
Wieder durch Rechnen, `rfl`.
:::
:::solution
```
rfl
```
:::
::::

::::leanonly (proof := "(f : Bool → Bool) (b : Bool) : f (f (f b)) = ⟦f b ‖ b, f b, f (f b)⟧") (lemma := "Bool.apply_apply_apply") (new := "revert, decide") (context := "Lean/WorldBool.lean") (group := "bool") (uses := "<;>, cases, decide, revert")
:::en
*Three times.* Whatever map `f : Bool → Bool` is: what does it do, applied three times? Check it for
`not` and for always `true`. In Lean the new tactics `revert` and `decide` check it, in every case at once.
:::

:::de
*Dreimal.* Welche Abbildung `f : Bool → Bool` auch immer: Was tut sie, dreimal angewandt? Prüf es
für `not` und für immer `true`. In Lean prüfen es die neuen Taktiken `revert` und `decide`, in allen Fällen auf einmal.
:::

:::proofen
No rule says what `f` does, so there is nothing to rewrite. But there are only four maps
`Bool → Bool`, and with the two values of `b` these are eight cases. Two new tactics: `revert f b`
takes the variables back into the statement, here `∀ f b, f (f (f b)) = f b`; `decide` reduces a
statement about finitely many cases until it is `true` or `false`, and so checks every case. (For
one unknown `f` there is nothing to compute: `decide` alone does not work.) Your result is unlocked
as `Bool.apply_apply_apply`.
:::

:::proofde
Keine Regel sagt, was `f` tut; es gibt also nichts umzuschreiben. Aber es gibt nur vier Abbildungen
`Bool → Bool`, und mit den zwei Werten von `b` sind das acht Fälle. Zwei neue Taktiken: `revert f b`
nimmt die Variablen zurück in die Aussage, hier `∀ f b, f (f (f b)) = f b`; `decide` reduziert eine
Aussage über endlich viele Fälle, bis sie `true` oder `false` ist, und prüft so jeden Fall. (Für ein
unbekanntes `f` gibt es nichts auszurechnen: `decide` allein geht nicht.) Dein Ergebnis wird als
`Bool.apply_apply_apply` freigeschaltet.
:::
:::solution
```
revert f b
decide
```
:::
:::solution
```
revert f
cases b <;> decide
```
:::
::::

::::leanonly (proof := "(f : Bool → Bool) (x : Bool) : ((bif f true then x else false) || (bif f true then false else x)) = ⟦x ‖ x, f true, !x⟧") (context := "Lean/WorldBool.lean") (group := "bool") (uses := "Bool.cond_false, Bool.false_or, Bool.cond_true, <;>, cases, rfl, rw")
:::en
*A test is `true` or `false`.* `x` behind the test `f true`, once in the `then` branch and once in
the `else` branch. What `f` does is unknown.
:::

:::de
*Ein Test ist `true` oder `false`.* `x` hinter dem Test `f true`, einmal im `then`-Zweig und einmal im
`else`-Zweig. Was `f` tut, ist unbekannt.
:::

:::proofen
`f true` is not a variable, but it is a `Bool`, so it is `true` or `false`: `cases f true` goes
through both values, as `cases x` does for a variable.
:::

:::proofde
`f true` ist keine Variable, aber ein `Bool`, also `true` oder `false`: `cases f true` geht beide
Werte durch, wie `cases x` für eine Variable.
:::
:::solution
```
cases f true <;> cases x <;> rfl
```
:::
:::solution
```
cases f true
rw [Bool.cond_false, Bool.cond_false, Bool.false_or]
rw [Bool.cond_true, Bool.cond_true]
cases x <;> rfl
```
:::
::::

::::leanonly (proof := "(f : Bool → Bool) (x y : ℕ) : (bif f true then x else 0) + (bif f true then y else 0) = bif f true then ⟦x + y ‖ x + y, x, y, x * y⟧ else 0") (lemma := "cond_add_cond") (context := "Lean/WorldBool.lean") (group := "bool") (uses := "Bool.cond_false, Bool.cond_true, <;>, cases, rfl, rw")
:::en
*Two numbers behind one test.* Twice the same test `f true`: once with `x`, once with `y`.
:::

:::de
*Zwei Zahlen hinter einem Test.* Zweimal derselbe Test `f true`: einmal mit `x`, einmal mit `y`.
:::

:::proofen
As in the level before, `cases f true`. You prove it for the test `f true` and numbers in `ℕ`; it
holds for every test `c : Bool`, and for masses too, and it is unlocked as
`cond_add_cond : (bif c then x else 0) + (bif c then y else 0) = bif c then x + y else 0`.
:::

:::proofde
Wie im Level davor, `cases f true`. Du beweist es für den Test `f true` und Zahlen in `ℕ`; es gilt
für jeden Test `c : Bool`, auch für Massen, und wird freigeschaltet als
`cond_add_cond : (bif c then x else 0) + (bif c then y else 0) = bif c then x + y else 0`.
:::
:::solution
```
cases f true <;> rfl
```
:::
:::solution
```
cases f true
rw [Bool.cond_false, Bool.cond_false, Bool.cond_false]
rw [Bool.cond_true, Bool.cond_true, Bool.cond_true]
```
:::
::::

::::quiz (tactic := "cases x <;> rfl") (statements := "(x : Bool) : (x && x) = x ;; (x : Bool) : x = true ;; (x : Bool) : (x || !x) = true ;; (x y : Bool) : (x && y) = (y && x) ;; (x : Bool) : (!x) = x ;; (x : Bool) : (true && x) = x") (answer := "1, 3, 6")
:::en
*Which ones?* Which of these statements does `cases x <;> rfl` prove?
:::

:::de
*Welche?* Welche dieser Aussagen beweist `cases x <;> rfl`?
:::
::::

::::leanonly (proof := "(x y : Bool) : (!(x && y)) = (!x || !y)") (lemma := "Bool.not_and") (context := "Lean/WorldBool.lean") (group := "bool") (uses := "Bool.false_and, Bool.not_false, Bool.true_or, Bool.true_and, Bool.not_true, Bool.false_or, <;>, cases, rfl, rw")
:::en
*De Morgan.* Not both `true` means: at least one of them is not `true`.
:::

:::de
*De Morgan.* Nicht beide `true` heißt: Mindestens eines von ihnen ist nicht `true`.
:::

:::proofen
Your result becomes the lemma `Bool.not_and`.
:::

:::proofde
Dein Ergebnis wird das Lemma `Bool.not_and`.
:::
:::solution
```
cases x <;> cases y <;> rfl
```
:::
:::solution
```
cases x
rw [Bool.false_and, Bool.not_false, Bool.true_or]
rw [Bool.true_and, Bool.not_true, Bool.false_or]
```
:::
:::solution
```
cases x <;> rfl
```
:::
:::solution
```
cases x
rw [Bool.false_and, Bool.not_false, Bool.true_or]
rfl
```
:::
::::

::::circuit (inputs := "x y") (gates := "not, and") (table := "0111") (goal := "x || y") (proof := "(x y : Bool) : (x || y) = !(!x && !y)") (lemma := "or_eq") (play := "a=not; b=not; c=and; d=not; x>a.0; y>b.0; a>c.0; b>c.1; c>d.0; d>out") (uses := "Bool.not_false, Bool.not_true, Bool.true_and, Bool.not_not, Bool.false_or, Bool.false_and, Bool.true_or, Bool.not_and, <;>, cases, rfl, rw")
:::hint (anchor := "none")
:::

:::en
*`or` from `and`.* An `or`, built without `or`: from `not` and `and` alone. Two inputs now.
:::

:::de
*`oder` aus `und`.* Ein `oder`, gebaut ohne `oder`: nur aus `nicht` und `und`. Jetzt mit zwei Eingängen.
:::

:::proofen
At least one is `true` exactly when not both are `false`. Two variables, so four cases: with `<;>`
in one line. Or without cases, with De Morgan from the level before. Your result becomes the lemma
`or_eq`.
:::

:::proofde
Mindestens eins ist `true` genau dann, wenn nicht beide `false` sind. Zwei Variablen, also vier Fälle:
mit `<;>` in einer Zeile. Oder ohne Fälle, mit De Morgan aus dem Level davor. Dein Ergebnis wird das
Lemma `or_eq`.
:::
:::solution
```
cases x <;> cases y <;> rfl
```
:::
:::solution
```
cases x
cases y
rfl
rfl
cases y
rfl
rfl
```
:::
:::solution
```
cases x <;> cases y
rw [Bool.not_false]
rfl
rw [Bool.not_false, Bool.not_true]
rfl
rw [Bool.not_true, Bool.not_false]
rfl
rw [Bool.not_true]
rfl
```
:::
:::solution
```
cases x
rw [Bool.not_false, Bool.true_and, Bool.not_not, Bool.false_or]
rw [Bool.not_true, Bool.false_and, Bool.not_false, Bool.true_or]
```
:::
:::solution
```
cases x
rw [Bool.not_false, Bool.true_and, Bool.not_not]
rfl
rw [Bool.not_true, Bool.false_and, Bool.not_false]
rfl
```
:::
:::solution
```
rw [Bool.not_and, Bool.not_not, Bool.not_not]
```
:::
::::

::::circuit (inputs := "x y") (gates := "and, or, not") (table := "0110") (goal := "x ^^ y") (proof := "(x y : Bool) : ((x || y) && !(x && y)) = (x ^^ y)") (play := "a=or; b=and; c=not; d=and; x>a.0; y>a.1; x>b.0; y>b.1; b>c.0; a>d.0; c>d.1; d>out") (uses := "Bool.false_or, Bool.false_and, Bool.not_false, Bool.true_or, Bool.true_and, Bool.not_and, Bool.not_true, <;>, cases, rfl, rw")
:::hint (anchor := "none")
:::

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
`x ^^ y` (*xor*) is `true` when exactly one of `x` and `y` is `true`.
:::

:::proofde
`x ^^ y` (*xor*) ist `true`, wenn genau eines von `x` und `y` `true` ist.
:::
:::solution
```
cases x <;> cases y <;> rfl
```
:::
:::solution
```
cases x
cases y
rfl
rfl
cases y
rfl
rfl
```
:::
:::solution
```
cases x
rw [Bool.false_or, Bool.false_and, Bool.not_false]
cases y <;> rfl
rw [Bool.true_or, Bool.true_and, Bool.true_and]
cases y <;> rfl
```
:::
:::solution
```
rw [Bool.not_and]
cases x
rw [Bool.false_or, Bool.not_false, Bool.true_or]
cases y <;> rfl
rw [Bool.true_or, Bool.true_and, Bool.not_true, Bool.false_or]
cases y <;> rfl
```
:::
::::
