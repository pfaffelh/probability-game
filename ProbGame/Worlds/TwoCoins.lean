import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Building with Coins" =>

%%%
htmlSplit := .never
%%%

:::en
The circuits of the world *Bool*, now with a coin at each input: `x ← coin p`, `y ← coin p`, …,
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
Die Schaltungen der Welt *Bool*, jetzt mit einer Münze an jedem Eingang: `x ← coin p`,
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
:::::leanonly (proof := "(p : I) : (bif false then coin p false else 0) + (bif !false then coin p true else 0) = ⟦↑p ‖ ↑p, ↑(σ p), 0, 1⟧") (new := "simp") (uses := "-")
::::hint (anchor := "gap")
:::en
Which of the two branches is taken, and what is the mass of the coin there?
:::

:::de
Welcher der beiden Zweige wird genommen, und was ist dort die Masse der Münze?
:::
::::

::::hint (anchor := "item:simp")
:::en
`simp`: the simplifier, with all rules marked simp.
:::

:::de
`simp`: der Simplifier, mit allen Regeln, die simp tragen.
:::
::::

:::en
*The simplifier.* What you did by hand so far, now in one move.
:::

:::de
*Der Simplifier.* Was du bisher von Hand gemacht hast, jetzt in einem Zug.
:::

:::proofen
By hand this is `rw [Bool.cond_false, zero_add, Bool.not_false, Bool.cond_true, coin_true]`: five
rules, each of them simple, and you know them all. From now on they go into the simplifier, `simp`. It
rewrites with a whole list of rules, again and again, until none applies any more, and it computes
with numbers.

Which rules are in the list? In the inventory they now carry the mark *simp*: among yours `coin_true`,
`coin_false`, `pure_true`, `pure_false`, `add_symm_eq_one`, `tsub_self`, `Bool.not_true`,
`Bool.not_false`, `Bool.not_not`, `Bool.and_self`, `Bool.cond_true`, `Bool.cond_false`, `Bool.cond_self`,
`Bool.true_beq`, `Bool.false_beq`, `beq_true`; and a few simple ones that are always there, such as
`zero_add`, `add_zero`, `mul_one` and `true && b = b`. Not in the list are rules like `bool_ext`, `map_true`, `mass_not` or `add_comm`:
they change what you prove, or could go on forever, and you apply them yourself. `simp [h]`
puts a rule `h` into the list for this one call.

*Tip.* `simp`.
:::

:::proofde
Von Hand ist das `rw [Bool.cond_false, zero_add, Bool.not_false, Bool.cond_true, coin_true]`: fünf
Regeln, jede einfach, und du kennst sie alle. Ab jetzt stecken wir sie in den Simplifier, `simp`. Er
schreibt mit einer ganzen Liste von Regeln um, immer wieder, bis keine mehr passt, und er rechnet mit
Zahlen.

Welche Regeln stehen in der Liste? Im Inventar tragen sie jetzt die Marke *simp*: von deinen `coin_true`,
`coin_false`, `pure_true`, `pure_false`, `add_symm_eq_one`, `tsub_self`, `Bool.not_true`,
`Bool.not_false`, `Bool.not_not`, `Bool.and_self`, `Bool.cond_true`, `Bool.cond_false`, `Bool.cond_self`,
`Bool.true_beq`, `Bool.false_beq`, `beq_true`; dazu ein paar einfache, die immer dabei sind, etwa
`zero_add`, `add_zero`, `mul_one` und `true && b = b`. Nicht in der Liste sind Regeln wie `bool_ext`, `map_true`, `mass_not` oder
`add_comm`: Sie ändern, was du beweist, oder könnten endlos laufen, und du wendest sie selbst an.
`simp [h]` nimmt eine Regel `h` für diesen einen Aufruf in die Liste auf.

*Tipp.* `simp`.
:::
:::solution
```
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

::::leanonly (proof := "(μ : DiscreteMeasure Bool) (f : Bool → DiscreteMeasure Bool) : (do let x ← μ; f x) = μ.bind f") (uses := "-")
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

*Tip.* `rfl`.
:::

:::proofde
Beide Seiten sind dasselbe, nur anders geschrieben.

*Tipp.* `rfl`.
:::
:::solution
```
rfl
```
:::
::::

:::::circuit (height := "440") (inputs := "x y") (gates := "") (coins := "p p") (target := "bool true:p false:1-p") (start := "a=and; a>out") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; pure (x && x)) = coin p") (new := "bind_pure") (play := "x>a.0; x>a.1") (uses := "Bool.and_self, bind_pure, pure_bind")
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

Your lemma `Bool.and_self : (x && x) = x` from *Bool*, and the rule `bind_pure : (do let x ← μ; pure x) = μ`. The `x` of
`let x ← coin p` is bound, as the `x` of `fun x => …` in *Maps*: so `simp_rw`, not `rw`. (Lean itself
reads `do let x ← μ; pure x` as `μ` at once, when you type it.)

*Tip.* `simp_rw [Bool.and_self, bind_pure]`.
:::

:::proofde
Auf dem Spielfeld ging die Münze `x` zweimal ins `and`; in Lean ist das `x && x`. `x` ist der Name
eines Zugs aus `coin p`, keine Zufallsvariable: Zweimal benutzt ist es zweimal derselbe Wert. Zwei
Münzen `x` und `y` wären zwei Züge, mit $`p^2` (bald, in `coin_and`). Was bleibt, `x` ziehen und
zurückgeben, ist `coin p` selbst.

Dein Lemma `Bool.and_self : (x && x) = x` aus *Bool* und die Regel `bind_pure : (do let x ← μ; pure x) = μ`. Das `x` von
`let x ← coin p` ist gebunden, wie das `x` von `fun x => …` in *Abbildungen*: also `simp_rw`, nicht
`rw`. (Lean selbst liest `do let x ← μ; pure x` sofort als `μ`, wenn du es eintippst.)

*Tipp.* `simp_rw [Bool.and_self, bind_pure]`.
:::
:::solution
```
simp_rw [Bool.and_self, bind_pure]
```
:::
:::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) (f : Bool → DiscreteMeasure Bool) : (do let x ← μ; f x) true = μ true * f true true + μ false * f false true") (new := "bind_apply") (lemma := "bind_true") (uses := "bind_apply, Fintype.sum_bool")
:::en
*Two ways to true.* The mass of `do let x ← μ; f x` at `true` comes two ways: the first draw is
`true`, or it is `false`.
:::

:::de
*Zwei Wege zu true.* Die Masse von `do let x ← μ; f x` bei `true` kommt auf zwei Wegen: Der erste
Zug ist `true`, oder er ist `false`.
:::

:::proofen
The definition of a draw sums over the first draw `a`: its mass, times the mass of what follows,

```
(do let a ← μ; f a) b = ∑' a, μ a * (f a) b
```

On a finite type, `∑'` is the finite sum `∑`, and that is the new rule
`bind_apply : (do let a ← μ; f a) b = ∑ a, μ a * f a b`. On `Bool` it has two summands
(`Fintype.sum_bool`). What you prove is unlocked as `bind_true`.

*Tip.* `rw [bind_apply, Fintype.sum_bool]`.
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

*Tipp.* `rw [bind_apply, Fintype.sum_bool]`.
:::
:::solution
```
rw [bind_apply, Fintype.sum_bool]
```
:::
::::

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

*Tip.* `ext b`, `rw [map_apply, bind_apply]`, `simp_rw [Fintype.sum_bool, pure_apply]`,
`cases f true <;> cases f false <;> cases b <;> simp`.
:::

:::proofde
Vergleiche die Massen bei jedem `b`: `ext b`, dann `map_apply` links und `bind_apply` rechts, und mit
`simp_rw [Fintype.sum_bool, pure_apply]` die Summen ausgeschrieben und die Massen von `pure`. Was `f`
tut, ist unbekannt, und `b` auch: `cases f true <;> cases f false <;> cases b`, acht Fälle, und in
jedem rechnet `simp`. Du beweist es auf `Bool`; es gilt für jeden Typ und wird in dieser allgemeinen
Form als `map_eq_pure_bind` freigeschaltet.

*Tipp.* `ext b`, `rw [map_apply, bind_apply]`, `simp_rw [Fintype.sum_bool, pure_apply]`,
`cases f true <;> cases f false <;> cases b <;> simp`.
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

::::circuit (height := "440") (inputs := "x y") (gates := "and, or, not") (coins := "p p") (target := "bool true:p^2 false:1-p^2") (context := "Lean/Rules.lean") (proof := "(p q : I) : (do let x ← coin p; let y ← coin q; pure (x && y)) = coin (p * q)") (lemma := "coin_and") (new := "mass_mul") (play := "a=and; x>a.0; y>a.1; a>out") (uses := "bool_ext, bind_true, mass_mul, bind_false")
:::en
*Both `true`.* Two coins, and `true` only when both show `true`.
:::

:::de
*Beide `true`.* Zwei Münzen, und `true` nur, wenn beide `true` zeigen.
:::

:::proofen
Your circuit, read from top to bottom, is a `do` block: `let x ← coin p`
throws a coin and calls its result `x`, and `pure` at the end is the result. Each `←` is a new throw,
independent of the others. Prove it for two coins `p` and `q` (on the board both were `p`): both
`true` with probability $`p \cdot q`. It becomes your lemma `coin_and`, independence itself.

Two distributions on `Bool` are equal when their masses at `true` are: `apply bool_ext`. Then
`bind_true`, three times: for the first draw, and for the second draw after `true` and after `false`.

Then the simplifier from the first level of this world. One new rule: `mass_mul : ↑(p * q) = ↑p * ↑q`,
the product `p * q` in $`[0, 1]` as a mass. It carries no mark simp, so give it along, `simp [mass_mul]`.

*Tip.* `apply bool_ext`, `rw [bind_true, bind_true, bind_true]`, `simp [mass_mul]`.
:::

:::proofde
Dein Schaltplan, von oben nach unten gelesen, ist ein `do`-Block: `let x ← coin p` wirft eine Münze
und nennt ihr Ergebnis `x`, und `pure` am Ende ist das Ergebnis. Jedes `←` ist ein neuer Wurf,
unabhängig von den anderen. Beweise es für zwei Münzen `p` und `q` (auf dem Spielfeld waren beide
`p`): beide `true` mit Wahrscheinlichkeit $`p \cdot q`. Es wird dein Lemma `coin_and`, die
Unabhängigkeit selbst.

Zwei Verteilungen auf `Bool` sind gleich, wenn ihre Massen bei `true` gleich sind: `apply bool_ext`.
Dann `bind_true`, dreimal: für den ersten Zug, und für den zweiten nach `true` und nach `false`.

Dann der Simplifier aus dem ersten Level dieser Welt. Eine neue Regel: `mass_mul : ↑(p * q) = ↑p * ↑q`,
das Produkt `p * q` in $`[0, 1]` als Masse. Sie trägt keine Marke simp, also gib sie mit, `simp [mass_mul]`.

*Tipp.* `apply bool_ext`, `rw [bind_true, bind_true, bind_true]`, `simp [mass_mul]`.
:::
:::solution
```
apply bool_ext
rw [bind_true, bind_true, bind_true]
simp [mass_mul]
```
:::
::::

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

*Tip.* `ext b`, `rw [bind_apply, bind_apply]`, `simp_rw [Fintype.sum_bool, map_apply, Fintype.sum_bool]`,
`cases f true <;> cases f false <;> simp [add_mul, add_comm]`.
:::

:::proofde
Zwei Verteilungen sind gleich, wenn ihre Massen bei jedem `b` gleich sind: `ext b`. Dann `bind_apply`
auf beiden Seiten, und mit `simp_rw [Fintype.sum_bool, map_apply, Fintype.sum_bool]` sind alle Summen
ausgeschrieben, auch die in `map_apply`. Was `f` tut, ist unbekannt: `cases f true` und `cases f false`
geben die vier möglichen `f`, und in jedem rechnet der Simplifier den Rest aus, mit der neuen Regel
`add_mul : (a + b) * c = a * c + b * c` und mit `add_comm` für die Reihenfolge. Mit `<;>` aus *Bool*
ist das eine Zeile. Du beweist es auf `Bool`; es gilt für jeden Typ und wird in dieser allgemeinen Form
als `bind_map_left` freigeschaltet.

*Tipp.* `ext b`, `rw [bind_apply, bind_apply]`, `simp_rw [Fintype.sum_bool, map_apply, Fintype.sum_bool]`,
`cases f true <;> cases f false <;> simp [add_mul, add_comm]`.
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

*Tip.* `ext b`, `rw [map_apply, bind_apply]`, `simp_rw [Fintype.sum_bool, bind_apply, map_apply, Fintype.sum_bool]`,
`cases f true <;> cases f false <;> cases b <;> simp [mul_add]`, then `rw [add_add_add_comm]` twice.
:::

:::proofde
Wie bei `bind_map_left`: `ext b`, `map_apply` und `bind_apply`, und alle Summen ausgeschrieben, auch
die inneren. Dann die vier möglichen `f` und die zwei `b`, und `simp` mit der neuen Regel
`mul_add : a * (b + c) = a * b + a * c`. Wo `f` konstant ist, bleiben zwei Summen aus vier Massen, in
anderer Reihenfolge: `add_add_add_comm : a + b + (c + d) = a + c + (b + d)`, einmal in jeder. Du
beweist es auf `Bool`; es gilt für jeden Typ und wird in dieser allgemeinen Form als `map_bind`
freigeschaltet.

*Tipp.* `ext b`, `rw [map_apply, bind_apply]`, `simp_rw [Fintype.sum_bool, bind_apply, map_apply, Fintype.sum_bool]`,
`cases f true <;> cases f false <;> cases b <;> simp [mul_add]`, dann zweimal `rw [add_add_add_comm]`.
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

::::circuit (height := "440") (inputs := "x y") (gates := "and, or, not") (coins := "p p") (target := "bool true:2p-p^2 false:(1-p)^2") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure (x || y)) = coin (σ (σ p * σ p))") (play := "a=or; x>a.0; y>a.1; a>out") (uses := "coin_not, coin_and, bind_map_left, map_bind, map_pure, or_eq")
:::en
*At least one `true`.* `false` only when both show `false`: $`(1 - p)^2`.
:::

:::de
*Mindestens einmal `true`.* `false` nur, wenn beide `false` zeigen: $`(1 - p)^2`.
:::

:::proofen
At least one `true` is: not both `false`, with probability $`1 - (1 - p)^2`. Your lemmas De
Morgan, `or_eq : (x || y) = !(!x && !y)` from *Bool*, and `map_bind` from the level before: a move
after a `do` block goes into it.

*Tip.* On the right side, backwards: `rw [← coin_not]`, `rw [← coin_and]`, `rw [← coin_not]`; then
`simp only [bind_map_left, map_bind, map_pure, or_eq]`.
:::

:::proofde
Mindestens einmal `true` heißt: nicht beide `false`, mit Wahrscheinlichkeit $`1 - (1 - p)^2`. Deine
Lemmas De Morgan, `or_eq : (x || y) = !(!x && !y)` aus *Bool*, und `map_bind` aus dem Level davor:
Ein Zug nach einem `do`-Block wandert in ihn hinein.

*Tipp.* Auf der rechten Seite, rückwärts: `rw [← coin_not]`, `rw [← coin_and]`, `rw [← coin_not]`;
dann `simp only [bind_map_left, map_bind, map_pure, or_eq]`.
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

*Tip.* `ext b`, `rw [bind_apply, Fintype.sum_bool, ← add_mul]`, `simp`.
:::

:::proofde
Bei jedem `b`: `ext b`, `bind_apply` und `Fintype.sum_bool`. Beide Wege machen mit demselben `ν b`
weiter, also zieh es heraus, mit `add_mul` rückwärts: `← add_mul`. Übrig sind die zwei Massen der
Münze, und sie ergeben zusammen eins: `simp`. Es wird als `coin_unused` freigeschaltet.

*Tipp.* `ext b`, `rw [bind_apply, Fintype.sum_bool, ← add_mul]`, `simp`.
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

*Tip.* `simp`, then `rw [coin_unused]`.
:::

:::proofde
`x && !x` ist nie `true`: dein Lemma `Bool.and_not_self` aus *Bool*, mit der Marke simp, also benutzt
es `simp`. Dann wird die Münze nicht mehr benutzt: `coin_unused` aus dem Level davor.

*Tipp.* `simp`, dann `rw [coin_unused]`.
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

::::circuit (inputs := "x y") (gates := "and, or, not") (coins := "p p") (target := "bool true:2p(1-p) false:p^2+(1-p)^2") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure ((x || y) && !(x && y))) = (do let x ← coin p; let y ← coin p; pure (xor x y))") (play := "a=or; b=and; c=not; d=and; x>a.0; y>a.1; x>b.0; y>b.1; b>c.0; a>d.0; c>d.1; d>out") (uses := "-")
:::en
*Boss: exactly one `true`*, without a function for it: at least one, but not both.
:::

:::de
*Endgegner: genau einmal `true`*, ohne eine Funktion dafür: mindestens einmal, aber nicht beide.
:::

:::proofen
*Boss.* Exactly one `true` is `xor`. Both sides throw the same coins; go under the throws, with `congr`
and `ext x` (and again for `y`), and look at all four cases, with `<;>` in one line.

*Tip.* `congr`, `ext x`, `congr`, `ext y`, `cases x <;> cases y <;> rfl`.
:::

:::proofde
*Endgegner.* Genau einmal `true` ist `xor`. Beide Seiten werfen dieselben Münzen; geh unter die Würfe, mit
`congr` und `ext x` (und nochmal für `y`), und sieh dir alle vier Fälle an, mit `<;>` in einer Zeile.

*Tipp.* `congr`, `ext x`, `congr`, `ext y`, `cases x <;> cases y <;> rfl`.
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
