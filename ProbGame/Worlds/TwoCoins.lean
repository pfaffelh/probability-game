import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Building with Coins" =>

%%%
htmlSplit := .never
%%%

:::en
The circuits of the world *Circuits*, now with a coin at each input: `x ← coin p`, `y ← coin p`, …,
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
Die Schaltungen der Welt *Schaltungen*, jetzt mit einer Münze an jedem Eingang: `x ← coin p`,
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

:::::circuit (height := "440") (inputs := "x y") (gates := "") (coins := "p p") (target := "bool true:p false:1-p") (start := "a=and; a>out") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; pure (x && x)) = coin p") (new := "simp only, Bool.and_self, bind_pure") (play := "x>a.0; x>a.1") (uses := "Bool.and_self, bind_pure, pure_bind")
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

Two rules: `Bool.and_self : (x && x) = x`, and `bind_pure : (do let x ← μ; pure x) = μ`. But `x && x`
stands after `let x ← coin p`, where `x` is a name of the `do` block, bound like the index `x` of a
sum `∑ x, …`; and `rw` rewrites only parts without such a name (`rw [Bool.and_self]` does not find
`x && x`, though it stands there).
The new tactic `simp only [rules]` can: it rewrites with the rules everywhere, also inside `do`
blocks, as often as it can, and closes the goal when the two sides become the same. (Lean itself reads
`do let x ← μ; pure x` as `μ` at once, when you type it.)

*Tip.* `simp only [Bool.and_self, bind_pure]`.
:::

:::proofde
Auf dem Spielfeld ging die Münze `x` zweimal ins `and`; in Lean ist das `x && x`. `x` ist der Name
eines Zugs aus `coin p`, keine Zufallsvariable: Zweimal benutzt ist es zweimal derselbe Wert. Zwei
Münzen `x` und `y` wären zwei Züge, mit $`p^2` (bald, in `coin_and`). Was bleibt, `x` ziehen und
zurückgeben, ist `coin p` selbst.

Zwei Regeln: `Bool.and_self : (x && x) = x` und `bind_pure : (do let x ← μ; pure x) = μ`. Aber
`x && x` steht nach `let x ← coin p`, wo `x` ein Name des `do`-Blocks ist, gebunden wie der Index `x`
einer Summe `∑ x, …`; und `rw` schreibt nur Teile ohne so einen Namen um (`rw [Bool.and_self]` findet
`x && x` nicht, obwohl es dasteht). Die neue Taktik `simp only [Regeln]` kann es: Sie schreibt mit den Regeln überall um,
auch in `do`-Blöcken, so oft es geht, und schließt das Ziel, wenn beide Seiten gleich werden. (Lean
selbst liest `do let x ← μ; pure x` sofort als `μ`, wenn du es eintippst.)

*Tipp.* `simp only [Bool.and_self, bind_pure]`.
:::
:::solution
```
simp only [Bool.and_self, bind_pure]
```
:::
:::::

:::::leanonly (proof := "(μ : DiscreteMeasure Bool) (f : Bool → Bool) : (do let x ← μ; pure (f x)) = μ.map f") (new := "map_eq_pure_bind") (uses := "map_eq_pure_bind")
::::hint (anchor := "statement")
:::en
A move `μ.map f` is a `do` block: draw `x` from `μ`, then `f x` for sure.
:::

:::de
Ein Zug `μ.map f` ist ein `do`-Block: `x` aus `μ` ziehen, dann sicher `f x`.
:::
::::

:::en
*A move is a `do` block.* A move `μ.map f` draws `x` from `μ` and computes `f x`, for sure:
`pure (f x)`.
:::

:::de
*Ein Zug ist ein `do`-Block.* Ein Zug `μ.map f` zieht `x` aus `μ` und rechnet `f x` aus, sicher:
`pure (f x)`.
:::

:::proofen
`map_eq_pure_bind : μ.map f = do let x ← μ; pure (f x)`.

*Tip.* `rw [map_eq_pure_bind]`.
:::

:::proofde
`map_eq_pure_bind : μ.map f = do let x ← μ; pure (f x)`.

*Tipp.* `rw [map_eq_pure_bind]`.
:::
:::solution
```
rw [map_eq_pure_bind]
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

::::leanonly (proof := "(p q : I) : coin (p * q) true = (↑p * ↑q : ENNReal)") (new := "mass_mul") (uses := "coin_true, mass_mul, coin_false, coin_total")
:::en
*A product of chances.* `p * q` is again a number in $`[0, 1]`, and as a mass it is the product of
the masses.
:::

:::de
*Ein Produkt von Chancen.* `p * q` ist wieder eine Zahl in $`[0, 1]`, und als Masse ist es das
Produkt der Massen.
:::

:::proofen
`mass_mul : ↑(p * q) = ↑p * ↑q`.

*Tip.* `rw [coin_true, mass_mul]`.
:::

:::proofde
`mass_mul : ↑(p * q) = ↑p * ↑q`.

*Tipp.* `rw [coin_true, mass_mul]`.
:::
:::solution
```
rw [coin_true, mass_mul]
```
:::
::::

::::circuit (height := "440") (inputs := "x y") (gates := "and, or, not") (coins := "p p") (target := "bool true:p^2 false:1-p^2") (context := "Lean/Rules.lean") (proof := "(p q : I) : (do let x ← coin p; let y ← coin q; pure (x && y)) = coin (p * q)") (lemma := "coin_and") (new := "norm_num") (play := "a=and; x>a.0; y>a.1; a>out") (uses := "bool_ext, bind_true, mass_mul, bind_false")
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

New from now on: `norm_num` does the computing for you. It computes with numbers and masses (`p * 1`,
`a + 0`, `bif true then a else b`, `true && b`, the masses `coin p true = p` and `(pure b) true`, and
taking away a finite mass), and with `norm_num [h]` also with a rule `h` of yours. What is left to you
are the rules of the game. From here on, `coin_true`, `Bool.cond_true` and the like are no longer rewritten one by one: after the step that splits (`bind_true`, `bind_false`), `norm_num`.

*Tip.* `apply bool_ext`, `rw [bind_true, bind_true, bind_true]`, `norm_num [mass_mul]`.
:::

:::proofde
Dein Schaltplan, von oben nach unten gelesen, ist ein `do`-Block: `let x ← coin p` wirft eine Münze
und nennt ihr Ergebnis `x`, und `pure` am Ende ist das Ergebnis. Jedes `←` ist ein neuer Wurf,
unabhängig von den anderen. Beweise es für zwei Münzen `p` und `q` (auf dem Spielfeld waren beide
`p`): beide `true` mit Wahrscheinlichkeit $`p \cdot q`. Es wird dein Lemma `coin_and`, die
Unabhängigkeit selbst.

Zwei Verteilungen auf `Bool` sind gleich, wenn ihre Massen bei `true` gleich sind: `apply bool_ext`.
Dann `bind_true`, dreimal: für den ersten Zug, und für den zweiten nach `true` und nach `false`.

Neu ab jetzt: `norm_num` rechnet für dich. Es rechnet mit Zahlen und Massen (`p * 1`, `a + 0`,
`bif true then a else b`, `true && b`, die Massen `coin p true = p` und `(pure b) true`, und das
Wegnehmen einer endlichen Masse), und mit `norm_num [h]` auch mit einer Regel `h` von dir. Was dir
bleibt, sind die Regeln des Spiels. Ab hier schreibst du `coin_true`, `Bool.cond_true` und Ähnliches nicht mehr einzeln um: nach dem Schritt, der aufteilt (`bind_true`, `bind_false`), `norm_num`.

*Tipp.* `apply bool_ext`, `rw [bind_true, bind_true, bind_true]`, `norm_num [mass_mul]`.
:::
:::solution
```
apply bool_ext
rw [bind_true, bind_true, bind_true]
norm_num [mass_mul]
```
:::
::::

::::leanonly (proof := "(p : I) (f : Bool → DiscreteMeasure Bool) : (do let x ← (coin p).map not; f x) = (do let x ← coin p; f (!x))") (new := "bind_map_left") (uses := "bind_map_left, map_bind")
:::en
*A move before a draw.* Drawing from a moved coin is drawing from the coin and moving the result.
:::

:::de
*Ein Zug vor dem Ziehen.* Aus einer bewegten Münze ziehen heißt, aus der Münze ziehen und das Ergebnis bewegen.
:::

:::proofen
`bind_map_left : (do let x ← μ.map f; g x) = (do let x ← μ; g (f x))`.

*Tip.* `rw [bind_map_left]`.
:::

:::proofde
`bind_map_left : (do let x ← μ.map f; g x) = (do let x ← μ; g (f x))`.

*Tipp.* `rw [bind_map_left]`.
:::
:::solution
```
rw [bind_map_left]
```
:::
::::

::::circuit (height := "540") (inputs := "x y") (gates := "and, or, not") (coins := "p p") (target := "bool true:p(1-p) false:1-p(1-p)") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure (x && !y)) = coin (p * σ p)") (play := "a=not; b=and; y>a.0; x>b.0; a>b.1; b>out") (uses := "coin_and, coin_not, bind_map_left, map_bind")
:::en
*First `true`, then `false`.*
:::

:::de
*Erst `true`, dann `false`.*
:::

:::proofen
Work backwards, on the right side: `rw [← coin_and]` uses the rule from right to left, and
`rw [← coin_not]` turns `coin (σ p)` into `(coin p).map not`. Then a gate sits inside the `do` block,
in `let y ← (coin p).map not`. The new rule
`bind_map_left : (do let x ← μ.map f; g x) = (do let x ← μ; g (f x))` takes the gate out of the draw
and into what is computed. But it is needed after `let x ← coin p`, where the name `x` of the `do`
block occurs: there `simp only`, not `rw`.

*Tip.* `rw [← coin_and]`, `rw [← coin_not]`, `simp only [bind_map_left]`.
:::

:::proofde
Arbeite rückwärts, auf der rechten Seite: `rw [← coin_and]` benutzt die Regel von rechts nach
links, und `rw [← coin_not]` macht aus `coin (σ p)` ein `(coin p).map not`. Dann steht ein Baustein im
`do`-Block, in `let y ← (coin p).map not`. Die neue Regel
`bind_map_left : (do let x ← μ.map f; g x) = (do let x ← μ; g (f x))` holt den Baustein aus dem Ziehen
heraus und in das Rechnen hinein. Gebraucht wird sie aber nach `let x ← coin p`, wo der Name `x` des
`do`-Blocks vorkommt: dort `simp only`, nicht `rw`.

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

::::leanonly (proof := "(p : I) (f : Bool → DiscreteMeasure Bool) : (do let x ← coin p; f x).map not = (do let x ← coin p; (f x).map not)") (new := "map_bind") (uses := "map_bind, bind_map_left")
:::en
*A move after a draw.* A move at the end can go into the `do` block.
:::

:::de
*Ein Zug nach dem Ziehen.* Ein Zug am Ende kann in den `do`-Block hinein.
:::

:::proofen
`map_bind : (do let x ← μ; g x).map f = (do let x ← μ; (g x).map f)`.

*Tip.* `rw [map_bind]`.
:::

:::proofde
`map_bind : (do let x ← μ; g x).map f = (do let x ← μ; (g x).map f)`.

*Tipp.* `rw [map_bind]`.
:::
:::solution
```
rw [map_bind]
```
:::
::::

::::leanonly (proof := "(x y : Bool) : (x || y) = !(!x && !y)") (lemma := "or_eq") (uses := "-")
:::en
*De Morgan.* `or` is `and` with three `not`s; the next level builds it so.
:::

:::de
*De Morgan.* `or` ist `and` mit drei `not`; das nächste Level baut es so.
:::

:::proofen
Four cases, each computed.

*Tip.* `cases x <;> cases y <;> rfl`.
:::

:::proofde
Vier Fälle, jeder ausgerechnet.

*Tipp.* `cases x <;> cases y <;> rfl`.
:::
:::solution
```
cases x <;> cases y <;> rfl
```
:::
::::

::::circuit (height := "440") (inputs := "x y") (gates := "and, or, not") (coins := "p p") (target := "bool true:2p-p^2 false:(1-p)^2") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure (x || y)) = coin (σ (σ p * σ p))") (play := "a=or; x>a.0; y>a.1; a>out") (uses := "coin_not, coin_and, bind_map_left, map_bind, map_pure, or_eq")
:::en
*At least one `true`.* `false` only when both show `false`: $`(1 - p)^2`.
:::

:::de
*Mindestens einmal `true`.* `false` nur, wenn beide `false` zeigen: $`(1 - p)^2`.
:::

:::proofen
At least one `true` is: not both `false`, with probability $`1 - (1 - p)^2`. Two new rules: De
Morgan, `or_eq : (x || y) = !(!x && !y)`, and `map_bind : (do let x ← μ; g x).map f = (do let x ← μ; (g x).map f)`:
a move after a `do` block goes into it.

*Tip.* On the right side, backwards: `rw [← coin_not]`, `rw [← coin_and]`, `rw [← coin_not]`; then
`simp only [bind_map_left, map_bind, map_pure, or_eq]`.
:::

:::proofde
Mindestens einmal `true` heißt: nicht beide `false`, mit Wahrscheinlichkeit $`1 - (1 - p)^2`. Zwei
neue Regeln: De Morgan, `or_eq : (x || y) = !(!x && !y)`, und
`map_bind : (do let x ← μ; g x).map f = (do let x ← μ; (g x).map f)`: Ein Zug nach einem `do`-Block
wandert in ihn hinein.

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

::::leanonly (proof := "(x : Bool) : (x && !x) = false") (lemma := "Bool.and_not_self") (uses := "-")
:::en
*Never both.* `x` and not `x` is never `true`.
:::

:::de
*Nie beides.* `x` und nicht `x` ist nie `true`.
:::

:::proofen
Two cases, each computed.

*Tip.* `cases x <;> rfl`.
:::

:::proofde
Zwei Fälle, jeder ausgerechnet.

*Tipp.* `cases x <;> rfl`.
:::
:::solution
```
cases x <;> rfl
```
:::
::::

::::leanonly (proof := "(p : I) : (do let _ ← coin p; pure true) = (pure true : DiscreteMeasure Bool)") (new := "coin_unused") (uses := "coin_unused, prob_unused")
:::en
*An unused coin.* A coin whose outcome is not used changes nothing.
:::

:::de
*Eine unbenutzte Münze.* Eine Münze, deren Ergebnis nicht benutzt wird, ändert nichts.
:::

:::proofen
`coin_unused : (do let _ ← coin p; ν) = ν` (`_`: the outcome gets no name, it is not used).

*Tip.* `rw [coin_unused]`.
:::

:::proofde
`coin_unused : (do let _ ← coin p; ν) = ν` (`_`: Das Ergebnis bekommt keinen Namen, es wird nicht benutzt).

*Tipp.* `rw [coin_unused]`.
:::
:::solution
```
rw [coin_unused]
```
:::
::::

::::circuit (height := "540") (inputs := "x") (gates := "and, or, not") (coins := "p") (target := "pure false") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; pure (x && !x)) = pure false") (play := "a=not; b=and; x>a.0; x>b.0; a>b.1; b>out") (uses := "Bool.and_not_self, coin_unused, Bool.or_not_self, prob_unused")
:::en
*Surely `false`, with a single coin.* A coin that goes into two functions is the same coin in both:
the results depend on each other.
:::

:::de
*Sicher `false`, mit einer einzigen Münze.* Eine Münze, die in zwei Funktionen geht, ist in beiden
dieselbe: Die Ergebnisse hängen voneinander ab.
:::

:::proofen
Two new rules: `Bool.and_not_self : (x && !x) = false`, and
`coin_unused : (do let _ ← coin p; ν) = ν`: a coin whose result is not used changes nothing.

*Tip.* `simp only [Bool.and_not_self]`, then `rw [coin_unused]`.
:::

:::proofde
Zwei neue Regeln: `Bool.and_not_self : (x && !x) = false`, und
`coin_unused : (do let _ ← coin p; ν) = ν`: Eine Münze, deren Ergebnis nicht benutzt wird, ändert
nichts.

*Tipp.* `simp only [Bool.and_not_self]`, dann `rw [coin_unused]`.
:::
:::solution
```
simp only [Bool.and_not_self]
rw [coin_unused]
```
:::
::::

::::leanonly (proof := "(x : Bool) : (x || !x) = true") (lemma := "Bool.or_not_self") (uses := "-")
:::en
*Always one of them.* `x` or not `x` is always `true`.
:::

:::de
*Immer eins von beiden.* `x` oder nicht `x` ist immer `true`.
:::

:::proofen
Two cases, each computed.

*Tip.* `cases x <;> rfl`.
:::

:::proofde
Zwei Fälle, jeder ausgerechnet.

*Tipp.* `cases x <;> rfl`.
:::
:::solution
```
cases x <;> rfl
```
:::
::::

::::circuit (height := "540") (inputs := "x") (gates := "and, or, not") (coins := "p") (target := "pure true") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; pure (x || !x)) = pure true") (play := "a=not; b=or; x>a.0; x>b.0; a>b.1; b>out") (uses := "Bool.or_not_self, coin_unused, Bool.and_not_self, prob_unused")
:::en
*Surely `true`, with a single coin.* As before, now with `or`: the coin or its flip shows `true`.
:::

:::de
*Sicher `true`, mit einer einzigen Münze.* Wie eben, jetzt mit `or`: Die Münze oder ihre Umkehrung
zeigt `true`.
:::

:::proofen
The new rule `Bool.or_not_self : (x || !x) = true`; the rest as in the level before.

*Tip.* `simp only [Bool.or_not_self]`, then `rw [coin_unused]`.
:::

:::proofde
Die neue Regel `Bool.or_not_self : (x || !x) = true`; der Rest wie im Level davor.

*Tipp.* `simp only [Bool.or_not_self]`, dann `rw [coin_unused]`.
:::
:::solution
```
simp only [Bool.or_not_self]
rw [coin_unused]
```
:::
::::

::::circuit (inputs := "x y") (gates := "and, or, not") (coins := "p p") (target := "bool true:2p(1-p) false:p^2+(1-p)^2") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure ((x || y) && !(x && y))) = (do let x ← coin p; let y ← coin p; pure (xor x y))") (play := "a=or; b=and; c=not; d=and; x>a.0; y>a.1; x>b.0; y>b.1; b>c.0; a>d.0; c>d.1; d>out") (uses := "-")
:::en
*Boss: exactly one `true`*, without a function for it: at least one, but not both.
:::

:::de
*Endgegner: genau einmal `true`*, ohne eine Funktion dafür: mindestens einmal, aber nicht beide.
:::

:::proofen
*Boss.* Exactly one `true` is `xor`. Both sides throw the same coins; go under the throws, with `congr 1`
and `funext x` (and again for `y`), and look at all four cases, with `<;>` in one line.

*Tip.* `congr 1`, `funext x`, `congr 1`, `funext y`, `cases x <;> cases y <;> rfl`.
:::

:::proofde
*Endgegner.* Genau einmal `true` ist `xor`. Beide Seiten werfen dieselben Münzen; geh unter die Würfe, mit
`congr 1` und `funext x` (und nochmal für `y`), und sieh dir alle vier Fälle an, mit `<;>` in einer Zeile.

*Tipp.* `congr 1`, `funext x`, `congr 1`, `funext y`, `cases x <;> cases y <;> rfl`.
:::
:::solution
```
congr 1
funext x
congr 1
funext y
cases x <;> cases y <;> rfl
```
:::
::::
