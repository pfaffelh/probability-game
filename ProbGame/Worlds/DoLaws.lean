import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Laws of `do`" =>

%%%
htmlSplit := .never
%%%

:::en
A gate before a coin, a gate after two coins, a coin that is not used: the circuits grow. Computing
every mass, as in *Two Coins*, grows faster: three coins have eight rows. This world goes another way:
laws that say how a circuit may be rebuilt without changing its distribution. On the board nothing is
new: coins at the inputs, and the distribution of the output is the target.
:::

:::proofen
A gate applied to a coin is a move, `(coin p).map not`; a throw is a draw, `let x ← coin p`. Three laws
say how moves and draws go together: a move is a `do` block; a move before a draw goes into what
follows; a move after a `do` block goes into it. You prove each of them on `Bool`, once, by computing
masses. Then it is yours for every type, and a `do` block is rewritten, not computed.
:::

:::de
Ein Baustein vor einer Münze, ein Baustein nach zwei Münzen, eine Münze, die nicht benutzt wird: Die
Schaltungen wachsen. Jede Masse auszurechnen, wie in *Zwei Münzen*, wächst schneller: Drei Münzen haben
acht Zeilen. Diese Welt geht einen anderen Weg: Gesetze, die sagen, wie man eine Schaltung umbauen darf,
ohne ihre Verteilung zu ändern. Auf dem Spielfeld ist nichts neu: Münzen an den Eingängen, und die
Verteilung des Ausgangs ist das Ziel.
:::

:::proofde
Ein Baustein, auf eine Münze angewandt, ist ein Zug, `(coin p).map not`; ein Wurf ist eine Ziehung,
`let x ← coin p`. Drei Gesetze sagen, wie Züge und Ziehungen zusammengehen: Ein Zug ist ein `do`-Block;
ein Zug vor einer Ziehung wandert in das, was folgt; ein Zug nach einem `do`-Block wandert in ihn
hinein. Du beweist jedes davon auf `Bool`, einmal, indem du Massen ausrechnest. Dann gehört es dir für
jeden Typ, und ein `do`-Block wird umgeschrieben, nicht ausgerechnet.
:::
:::::leanonly (proof := "(μ : DiscreteMeasure Bool) (f : Bool → Bool) : μ.map f = (do let x ← μ; ⟦pure (f x) ‖ pure (f x), pure x, μ.map f⟧)") (lemma := "map_eq_pure_bind") (uses := "map_apply, bind_apply, Fintype.sum_bool, pure_apply")
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
Compare the masses at every `b`: `ext b`, then `map_apply` on the left and `bind_apply` on the right,
and with `simp_rw [Fintype.sum_bool, pure_apply]` the sums written out and the masses of `pure`. What
`f` does is unknown, and so is `b`: `cases f true <;> cases f false <;> cases b`, eight cases, and in
each `simp` computes. You prove it on `Bool`; it holds for every type, and it is unlocked as
`map_eq_pure_bind` in this general form.
:::

:::proofde
Vergleiche die Massen bei jedem `b`: `ext b`, dann `map_apply` links und `bind_apply` rechts, und mit
`simp_rw [Fintype.sum_bool, pure_apply]` die Summen ausgeschrieben und die Massen von `pure`. Was `f`
tut, ist unbekannt, und `b` auch: `cases f true <;> cases f false <;> cases b`, acht Fälle, und in
jedem rechnet `simp`. Du beweist es auf `Bool`; es gilt für jeden Typ und wird in dieser allgemeinen
Form als `map_eq_pure_bind` freigeschaltet.
:::
:::solution
```
ext b
rw [map_apply, bind_apply]
simp_rw [Fintype.sum_bool, pure_apply]
cases f true <;> cases f false <;> cases b <;> simp
```
:::
:::::

:::::leanonly (proof := "(μ : DiscreteMeasure Bool) (f : Bool → Bool) (g : Bool → DiscreteMeasure Bool) : (do let x ← μ.map f; g x) = (do let x ← μ; ⟦g (f x) ‖ g (f x), g x, (g x).map f⟧)") (lemma := "bind_map_left") (new := "add_mul") (uses := "bind_apply, Fintype.sum_bool, map_apply, add_mul, add_comm, add_assoc")
::::hint (anchor := "gap")
:::en
First move with `f`, then go on with `g`: in one draw, with what does `g` go on?
:::

:::de
Erst mit `f` bewegen, dann mit `g` weitermachen: In einem Zug, womit macht `g` weiter?
:::
::::

:::en
*A move before a draw.* Drawing from a moved distribution is drawing from the distribution and moving
the result.
:::

:::de
*Ein Zug vor dem Ziehen.* Aus einer bewegten Verteilung ziehen heißt, aus der Verteilung ziehen und das
Ergebnis bewegen.
:::

:::proofen
Two distributions are equal when their masses at every `b` are: `ext b`. Then `bind_apply` on both
sides, and with `simp_rw [Fintype.sum_bool, map_apply, Fintype.sum_bool]` all sums written out, also
those inside `map_apply`. What `f` does is unknown: `cases f true` and `cases f false` give the four
possible `f`, and in each the simplifier computes the rest, with the new rule
`add_mul : (a + b) * c = a * c + b * c` and with `add_comm` for the order. With `<;>` from *Bool*
it is one line. You prove it on `Bool`; it holds for every type, and it is unlocked as `bind_map_left`
in this general form.
:::

:::proofde
Zwei Verteilungen sind gleich, wenn ihre Massen bei jedem `b` gleich sind: `ext b`. Dann `bind_apply`
auf beiden Seiten, und mit `simp_rw [Fintype.sum_bool, map_apply, Fintype.sum_bool]` sind alle Summen
ausgeschrieben, auch die in `map_apply`. Was `f` tut, ist unbekannt: `cases f true` und `cases f false`
geben die vier möglichen `f`, und in jedem rechnet der Simplifier den Rest aus, mit der neuen Regel
`add_mul : (a + b) * c = a * c + b * c` und mit `add_comm` für die Reihenfolge. Mit `<;>` aus *Bool*
ist das eine Zeile. Du beweist es auf `Bool`; es gilt für jeden Typ und wird in dieser allgemeinen Form
als `bind_map_left` freigeschaltet.
:::
:::solution
```
ext b
rw [bind_apply, bind_apply]
simp_rw [Fintype.sum_bool, map_apply, Fintype.sum_bool]
cases f true <;> cases f false <;> simp [add_mul, add_comm]
```
:::
:::::

::::circuit (height := "540") (inputs := "x y") (gates := "and, or, not") (coins := "p p") (target := "bool true:p(1-p) false:1-p(1-p)") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure (x && !y)) = coin (p * σ p)") (new := "simp only") (play := "a=not; b=and; y>a.0; x>b.0; a>b.1; b>out") (uses := "coin_and, coin_not, bind_map_left, map_bind")
:::en
*First `true`, then `false`.*
:::

:::de
*Erst `true`, dann `false`.*
:::

:::proofen
Work backwards, on the right side: `rw [← coin_and]` uses the rule from right to left, and
`rw [← coin_not]` turns `coin (σ p)` into `(coin p).map not`. Then a gate sits inside the `do` block,
in `let y ← (coin p).map not`. Your lemma from the level before,
`bind_map_left : (do let x ← μ.map f; g x) = (do let x ← μ; g (f x))` takes the gate out of the draw
and into what is computed. But it is needed after `let x ← coin p`, where the name `x` of the `do`
block occurs, bound. There `simp_rw [bind_map_left]` works; here the new tactic `simp only [rules]`
does too: the simplifier, but with only the rules you give, as often as it can; it closes the goal
when the two sides become the same.

*Tip.* `rw [← coin_and]`, `rw [← coin_not]`, `simp only [bind_map_left]`.
:::

:::proofde
Arbeite rückwärts, auf der rechten Seite: `rw [← coin_and]` benutzt die Regel von rechts nach
links, und `rw [← coin_not]` macht aus `coin (σ p)` ein `(coin p).map not`. Dann steht ein Baustein im
`do`-Block, in `let y ← (coin p).map not`. Dein Lemma aus dem Level davor,
`bind_map_left : (do let x ← μ.map f; g x) = (do let x ← μ; g (f x))` holt den Baustein aus dem Ziehen
heraus und in das Rechnen hinein. Gebraucht wird sie aber nach `let x ← coin p`, wo der Name `x` des
`do`-Blocks vorkommt, gebunden. Dort geht `simp_rw [bind_map_left]`; hier tut es auch die neue Taktik
`simp only [Regeln]`: der Simplifier, aber nur mit den Regeln, die du angibst, so oft es geht; er
schließt das Ziel, wenn beide Seiten gleich werden.

*Tipp.* `rw [← coin_and]`, `rw [← coin_not]`, `simp only [bind_map_left]`.
:::
:::solution
```
rw [← coin_and]
rw [← coin_not]
simp only [bind_map_left]
```
:::
::::

:::::leanonly (proof := "(μ : DiscreteMeasure Bool) (g : Bool → DiscreteMeasure Bool) (f : Bool → Bool) : (do let x ← μ; g x).map f = (do let x ← μ; ⟦(g x).map f ‖ (g x).map f, g (f x), g x⟧)") (lemma := "map_bind") (new := "mul_add, add_add_add_comm") (uses := "map_apply, bind_apply, Fintype.sum_bool, mul_add, add_add_add_comm")
::::hint (anchor := "gap")
:::en
A move after the whole draw: where can it go inside?
:::

:::de
Ein Zug nach dem ganzen Ziehen: Wohin kann er hinein?
:::
::::

:::en
*A move after a draw.* A move at the end can go into the `do` block.
:::

:::de
*Ein Zug nach dem Ziehen.* Ein Zug am Ende kann in den `do`-Block hinein.
:::

:::proofen
As for `bind_map_left`: `ext b`, `map_apply` and `bind_apply`, and all sums written out, also those
inside. Then the four possible `f` and the two `b`, and `simp` with the new rule
`mul_add : a * (b + c) = a * b + a * c`. Where `f` is constant, two sums of four masses are left, in
another order: `add_add_add_comm : a + b + (c + d) = a + c + (b + d)`, once in each. You prove it on
`Bool`; it holds for every type, and it is unlocked as `map_bind` in this general form.
:::

:::proofde
Wie bei `bind_map_left`: `ext b`, `map_apply` und `bind_apply`, und alle Summen ausgeschrieben, auch
die inneren. Dann die vier möglichen `f` und die zwei `b`, und `simp` mit der neuen Regel
`mul_add : a * (b + c) = a * b + a * c`. Wo `f` konstant ist, bleiben zwei Summen aus vier Massen, in
anderer Reihenfolge: `add_add_add_comm : a + b + (c + d) = a + c + (b + d)`, einmal in jeder. Du
beweist es auf `Bool`; es gilt für jeden Typ und wird in dieser allgemeinen Form als `map_bind`
freigeschaltet.
:::
:::solution
```
ext b
rw [map_apply, bind_apply]
simp_rw [Fintype.sum_bool, bind_apply, map_apply, Fintype.sum_bool]
cases f true <;> cases f false <;> cases b <;> simp [mul_add]
rw [add_add_add_comm]
rw [add_add_add_comm]
```
:::
:::::

:::::leanonly (proof := "(p : I) (ν : DiscreteMeasure Bool) : (do let _ ← coin p; ν) = ⟦ν ‖ ν, coin p, pure true⟧") (lemma := "coin_unused") (uses := "bind_apply, Fintype.sum_bool, add_mul")
::::hint (anchor := "gap")
:::en
The outcome of the coin is not used (`_`): what is left?
:::

:::de
Das Ergebnis der Münze wird nicht benutzt (`_`): Was bleibt?
:::
::::

:::en
*An unused coin.* A coin whose outcome is not used changes nothing.
:::

:::de
*Eine unbenutzte Münze.* Eine Münze, deren Ergebnis nicht benutzt wird, ändert nichts.
:::

:::proofen
At every `b`: `ext b`, `bind_apply` and `Fintype.sum_bool`. Both ways go on with the same `ν b`, so
take it out, with `add_mul` backwards: `← add_mul`. What is left are the two masses of the coin, and
they add up to one: `simp`. It is unlocked as `coin_unused`.
:::

:::proofde
Bei jedem `b`: `ext b`, `bind_apply` und `Fintype.sum_bool`. Beide Wege machen mit demselben `ν b`
weiter, also zieh es heraus, mit `add_mul` rückwärts: `← add_mul`. Übrig sind die zwei Massen der
Münze, und sie ergeben zusammen eins: `simp`. Es wird als `coin_unused` freigeschaltet.
:::
:::solution
```
ext b
rw [bind_apply, Fintype.sum_bool, ← add_mul]
simp
```
:::
:::::

::::circuit (height := "540") (inputs := "x") (gates := "and, or, not") (coins := "p") (target := "pure false") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; pure (x && !x)) = pure false") (play := "a=not; b=and; x>a.0; x>b.0; a>b.1; b>out") (uses := "coin_unused, prob_unused")
:::en
*Surely `false`, with a single coin.* A coin that goes into two functions is the same coin in both:
the results depend on each other.
:::

:::de
*Sicher `false`, mit einer einzigen Münze.* Eine Münze, die in zwei Funktionen geht, ist in beiden
dieselbe: Die Ergebnisse hängen voneinander ab.
:::

:::proofen
`x && !x` is never `true`: your lemma `Bool.and_not_self` from *Bool*, marked simp, so `simp` uses it.
Then the coin is no longer used: `coin_unused` from the level before.
:::

:::proofde
`x && !x` ist nie `true`: dein Lemma `Bool.and_not_self` aus *Bool*, mit der Marke simp, also benutzt
es `simp`. Dann wird die Münze nicht mehr benutzt: `coin_unused` aus dem Level davor.
:::
:::solution
```
simp
rw [coin_unused]
```
:::
::::

:::::leanonly (proof := "(p : I) : (do let x ← coin p; pure (x && x)) = (do let x ← coin p; pure ⟦x || x ‖ x || x, !x, x && !x⟧)") (new := "congr") (uses := "-")
::::hint (anchor := "gap")
:::en
Which result is the same as `x && x`, for every `x`?
:::

:::de
Welches Ergebnis ist dasselbe wie `x && x`, für jedes `x`?
:::
::::

:::en
*The same coin, two results.* Both sides throw the same coin and differ only in what they do with it.
:::

:::de
*Dieselbe Münze, zwei Ergebnisse.* Beide Seiten werfen dieselbe Münze und unterscheiden sich nur darin,
was sie damit tun.
:::

:::proofen
A new tactic: `congr` reduces the goal to the parts in which the two sides differ, here what comes after
the throw, as a function of `x`. Then `ext x` (from *One Coin*): equal for every `x`. Then two cases.

*Tip.* `congr`, `ext x`, `cases x <;> rfl`.
:::

:::proofde
Eine neue Taktik: `congr` führt das Ziel auf die Teile zurück, in denen sich die beiden Seiten
unterscheiden, hier das, was nach dem Wurf kommt, als Funktion von `x`. Dann `ext x` (aus *Eine Münze*):
gleich für jedes `x`. Dann zwei Fälle.

*Tipp.* `congr`, `ext x`, `cases x <;> rfl`.
:::
:::solution
```
congr
ext x
cases x <;> rfl
```
:::
:::::

::::circuit (height := "540") (inputs := "x y") (gates := "or, not") (coins := "p p") (target := "bool true:1-p^2 false:p^2") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure (!x || !y)) = (do let x ← coin p; let y ← coin p; pure (!(x && y)))") (play := "a=not; b=not; c=or; x>a.0; y>b.0; a>c.0; b>c.1; c>out") (uses := "-")
:::en
*Not both `true`*, without an `and`: only `or` and `not` are there.
:::

:::de
*Nicht beide `true`*, ohne ein `and`: Es gibt nur `or` und `not`.
:::

:::proofen
Both sides throw the same two coins and differ only in what they compute. So `congr` and `ext`, once
for each coin; then four cases.
:::

:::proofde
Beide Seiten werfen dieselben zwei Münzen und unterscheiden sich nur darin, was sie rechnen. Also
`congr` und `ext`, einmal für jede Münze; dann vier Fälle.
:::
:::solution
```
congr
ext x
congr
ext y
cases x <;> cases y <;> rfl
```
:::
::::

::::circuit (height := "440") (inputs := "x y") (gates := "and, or, not") (coins := "p p") (target := "bool true:2p-p^2 false:(1-p)^2") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure (x || y)) = coin (σ (σ p * σ p))") (play := "a=or; x>a.0; y>a.1; a>out") (uses := "coin_not, coin_and, bind_map_left, map_bind, map_pure, or_eq")
:::en
*Boss: at least one `true`.* `false` only when both show `false`: $`(1 - p)^2`.
:::

:::de
*Endgegner: mindestens einmal `true`.* `false` nur, wenn beide `false` zeigen: $`(1 - p)^2`.
:::

:::solution
```
rw [← coin_not]
rw [← coin_and]
rw [← coin_not]
simp only [bind_map_left, map_bind, map_pure, or_eq]
```
:::
::::
