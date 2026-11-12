import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "True and False" =>

%%%
htmlSplit := .never
number := false
%%%

:::en
Before chance: Lean's `Bool`, the type with the two values `true` and `false`.
A coin lies on the table, surely on one side. A *move* is a map `Bool → Bool`: `not` flips the coin,
*always true* lays it on `true`, *always false* on `false`. These are the moves of the coins in the
worlds to come; here the result is sure. Lean computes with them: `!true`, that is `not true`, is
`false`.
:::

:::de
Vor dem Zufall: `Bool` in Lean, der Typ mit den zwei Werten `true` und `false`.
Eine Münze liegt auf dem Tisch, sicher auf einer Seite. Ein *Zug* ist eine Abbildung `Bool → Bool`:
`not` dreht die Münze um, *immer true* legt sie auf `true`, *immer false* auf `false`. Das sind die
Züge der Münzen in den Welten danach; hier ist das Ergebnis sicher. Lean rechnet mit ihnen: `!true`,
also `not true`, ist `false`.
:::

::::boolean (inputs := "true") (target := "false") (moves := "not") (proof := ": (!true) = false") (new := "rfl") (play := "not")
:::en
*Flip.* The coin lies on `true`. Flip it onto the flag. Below the board is the move as Lean writes
it, and what Lean makes of it.
:::

:::de
*Umdrehen.* Die Münze liegt auf `true`. Dreh sie auf die Fahne. Unter dem Spielfeld steht der Zug,
wie Lean ihn schreibt, und was Lean daraus macht.
:::

:::proofen
*Now the proof.* What the board showed, now in Lean: `!true` is `not true`, and the statement is
`(!true) = false`. Below is the *goal*, what is to be shown. You prove it one *tactic* after
another; the tactics and rules you have are in the *inventory*, which grows from level to level.

The tactic `rfl` closes a goal whose two sides are the same after computing, and Lean knows how
`not` acts on `true`. Type `rfl` (or tap it in the inventory) and press *Run*.
:::

:::proofde
*Jetzt der Beweis.* Was das Spielfeld gezeigt hat, jetzt in Lean: `!true` ist `not true`, und die
Aussage ist `(!true) = false`. Unten steht das *Ziel*, also das, was zu zeigen ist. Du beweist es
mit einer *Taktik* nach der anderen; die Taktiken und Regeln, die du hast, stehen im *Inventar*, das
von Level zu Level wächst.

Die Taktik `rfl` schließt ein Ziel, dessen beide Seiten nach Ausrechnen gleich sind, und Lean weiß,
was `not` mit `true` macht. Tippe `rfl` ein (oder tippe es im Inventar an) und drücke *Ausführen*.
:::
:::solution
```
rfl
```
:::
::::

::::boolean (inputs := "true") (target := "true") (moves := "not") (proof := ": (!(!true)) = true") (new := "rw, Bool.not_true, Bool.not_false") (play := "not, not")
:::en
*Back again.* Bring the coin back to `true`, with flips only.
:::

:::de
*Wieder zurück.* Bring die Münze wieder auf `true`, nur mit Umdrehen.
:::

:::proofen
`rfl` would compute this as well. Here with rules, one step at a time. The tactic
`rw [Bool.not_true]` *rewrites* the goal with the rule `Bool.not_true : (!true) = false`: it
replaces the left side of the rule by its right side. Then the rule
`Bool.not_false : (!false) = true`. When both sides of the goal are the same, `rw` closes it.

*Tip.* `rw [Bool.not_true, Bool.not_false]`.
:::

:::proofde
`rfl` würde auch das ausrechnen. Hier mit Regeln, Schritt für Schritt. Die Taktik
`rw [Bool.not_true]` *schreibt* das Ziel mit der Regel `Bool.not_true : (!true) = false` *um*: Sie
ersetzt die linke Seite der Regel durch ihre rechte. Dann die Regel
`Bool.not_false : (!false) = true`. Sind beide Seiten des Ziels gleich, schließt `rw` es.

*Tipp.* `rw [Bool.not_true, Bool.not_false]`.
:::
:::solution
```
rw [Bool.not_true, Bool.not_false]
```
:::
::::

::::boolean (inputs := "false true") (target := "true true") (moves := "not, false") (proof := "(b : Bool) : (!((fun _ => false) b)) = true") (play := "false, not")
:::en
*Always true, without always true.* Now there are two coins: one on `false`, one on `true`. The board
plays your moves on both at once, for every value `b`. Lay both on `true`. There is no move
*always true*.
:::

:::de
*Immer true, ohne immer true.* Jetzt gibt es zwei Münzen: eine auf `false`, eine auf `true`. Das
Spielfeld spielt deine Züge auf beiden zugleich, für jeden Wert `b`. Leg beide auf `true`. Einen Zug
*immer true* gibt es nicht.
:::

:::proofen
`fun _ => false` is the map *always false*: it forgets its argument. So `(fun _ => false) b` is
`false`, whatever `b` is, and `!false` is `true`. Lean computes both: `rfl` proves the statement for
every `b` at once.
:::

:::proofde
`fun _ => false` ist die Abbildung *immer false*: Sie vergisst ihr Argument. Also ist
`(fun _ => false) b` gleich `false`, was immer `b` ist, und `!false` ist `true`. Lean rechnet beides
aus: `rfl` beweist die Aussage für jedes `b` auf einmal.
:::
:::solution
```
rfl
```
:::
::::

::::boolean (inputs := "false true") (target := "false true") (moves := "not") (proof := "(b : Bool) : (!(!b)) = b") (lemma := "Bool.not_not") (new := "cases, decide") (play := "not, not")
:::en
*Flipped twice.* Bring both coins back to where they lay.
:::

:::de
*Zweimal umgedreht.* Bring beide Münzen wieder dorthin, wo sie lagen.
:::

:::proofen
`!(!b) = b` for every `b`. Now `rfl` does not help: Lean cannot compute `!b` as long as it does not
know `b`. The tactic `cases b` splits into the cases `false` and `true`, two goals, one after the
other, as the two rows of the board. Each of them is computing.

Faster: the tactic `decide` computes a statement about `Bool` and so decides it. `decide +revert`
first takes the variables into the statement, here `∀ b, (!(!b)) = b`, and checks every case. From
now on it does the computing in `Bool` for you. Your result becomes the lemma `Bool.not_not`, as it
is called in Lean.

*Tip.* `decide +revert`. Or by hand: `cases b`, `rfl`, `rfl`.
:::

:::proofde
`!(!b) = b` für jedes `b`. Jetzt hilft `rfl` nicht: Lean kann `!b` nicht ausrechnen, solange es `b`
nicht kennt. Die Taktik `cases b` teilt in die Fälle `false` und `true`, zwei Ziele, eines nach dem
anderen, wie die zwei Zeilen des Spielfelds. Jedes davon ist Rechnen.

Schneller: Die Taktik `decide` rechnet eine Aussage über `Bool` aus und entscheidet sie so.
`decide +revert` nimmt zuerst die Variablen in die Aussage, hier `∀ b, (!(!b)) = b`, und prüft jeden
Fall. Ab jetzt übernimmt es das Rechnen in `Bool` für dich. Dein Ergebnis wird das Lemma
`Bool.not_not`, wie es in Lean heißt.

*Tipp.* `decide +revert`. Oder von Hand: `cases b`, `rfl`, `rfl`.
:::
:::solution
```
decide +revert
```
:::
::::

::::boolean (inputs := "false true") (target := "false true") (moves := "not, true, false") (count := "2") (proof := ": not ∘ not = (id : Bool → Bool)") (play := "not, not")
:::en
*Two moves, one map.* Bring both coins back again, in two moves, now with all three moves at hand.
Two moves one after the other are one map: `not ∘ not`, first `not`, then `not`.
:::

:::de
*Zwei Züge, eine Abbildung.* Bring beide Münzen wieder zurück, in zwei Zügen, jetzt mit allen drei
Zügen zur Wahl. Zwei Züge nacheinander sind eine Abbildung: `not ∘ not`, erst `not`, dann `not`.
:::

:::proofen
Now an equation between maps: `not ∘ not` is `id`, the map that does nothing. Two maps
`Bool → Bool` are the same when they agree at `false` and at `true`, and `decide` checks that too.

*Tip.* `decide`.
:::

:::proofde
Jetzt eine Gleichung zwischen Abbildungen: `not ∘ not` ist `id`, die Abbildung, die nichts tut. Zwei
Abbildungen `Bool → Bool` sind gleich, wenn sie bei `false` und bei `true` übereinstimmen, und auch
das prüft `decide`.

*Tipp.* `decide`.
:::
:::solution
```
decide
```
:::
::::

::::boolean (inputs := "true") (target := "true") (moves := "not, true, false") (count := "2") (proof := "(f : Bool → Bool) (h : f true = true) : f (f true) = true") (play := "true, true")
:::en
*The same move twice.* Two moves, and the coin lies on `true` again. Which moves `f` can you play
twice for this?
:::

:::de
*Zweimal derselbe Zug.* Zwei Züge, und die Münze liegt wieder auf `true`. Welche Züge `f` kannst du
dafür zweimal spielen?
:::

:::proofen
A move `f` that sends `true` to `true`, the hypothesis `h : f true = true`, does so twice. `rw [h]`
rewrites with the hypothesis: `f true` becomes `true`, wherever it stands in the goal.

*Tip.* `rw [h, h]`.
:::

:::proofde
Ein Zug `f`, der `true` nach `true` schickt, die Annahme `h : f true = true`, tut das auch zweimal.
`rw [h]` schreibt mit der Annahme um: `f true` wird `true`, wo immer es im Ziel steht.

*Tipp.* `rw [h, h]`.
:::
:::solution
```
rw [h, h]
```
:::
::::

::::boolean (inputs := "false true") (target := "true false") (moves := "not, true, false") (count := "3") (proof := "(f : Bool → Bool) (b : Bool) : f (f (f b)) = f b") (play := "not, not, not")
:::en
*The boss: three times is once.* Three moves, and both coins are flipped, as after one flip. In
fact, for every move `f`, playing it three times is the same as playing it once:
`f (f (f b)) = f b`.
:::

:::de
*Der Endgegner: Dreimal ist einmal.* Drei Züge, und beide Münzen sind umgedreht, wie nach einmal
Umdrehen. Tatsächlich ist jeder Zug `f`, dreimal gespielt, dasselbe wie einmal:
`f (f (f b)) = f b`.
:::

:::proofen
No rule says what `f` does. But there are only four maps `Bool → Bool`: `id`, `not`, always `true`,
always `false`, the moves of the coins in the worlds to come. With the two values of `b` these are
eight cases, and `decide +revert` checks them all. From the next world on, this no longer works: a
coin `coin p` is a different distribution for every number `p` between 0 and 1, infinitely many
cases. There, the rules do the work.

*Tip.* `decide +revert`.
:::

:::proofde
Keine Regel sagt, was `f` tut. Aber es gibt nur vier Abbildungen `Bool → Bool`: `id`, `not`, immer
`true`, immer `false`, die Züge der Münzen in den Welten danach. Mit den zwei Werten von `b` sind das
acht Fälle, und `decide +revert` prüft sie alle. Ab der nächsten Welt geht das nicht mehr: Eine Münze
`coin p` ist für jede Zahl `p` zwischen 0 und 1 eine andere Verteilung, unendlich viele Fälle. Dort
machen die Regeln die Arbeit.

*Tipp.* `decide +revert`.
:::
:::solution
```
decide +revert
```
:::
::::
