import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Two Coins" =>

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

New: the rule `bind_pure : (do let x ← μ; pure x) = μ`. The `x` of `let x ← coin p` is bound, as the
`x` of `fun x => …` in *Maps*. (Lean itself reads `do let x ← μ; pure x` as `μ` at once, when you
type it.)
:::

:::proofde
Auf dem Spielfeld ging die Münze `x` zweimal ins `and`; in Lean ist das `x && x`. `x` ist der Name
eines Zugs aus `coin p`, keine Zufallsvariable: Zweimal benutzt ist es zweimal derselbe Wert. Zwei
Münzen `x` und `y` wären zwei Züge, mit $`p^2` (bald, in `coin_and`). Was bleibt, `x` ziehen und
zurückgeben, ist `coin p` selbst.

Neu: die Regel `bind_pure : (do let x ← μ; pure x) = μ`. Das `x` von `let x ← coin p` ist gebunden,
wie das `x` von `fun x => …` in *Abbildungen*. (Lean selbst liest `do let x ← μ; pure x` sofort als
`μ`, wenn du es eintippst.)
:::
:::solution
```
simp_rw [Bool.and_self, bind_pure]
```
:::
:::::

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
::::

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
So far every rule by hand, one at a time. From now on the simple ones go into the simplifier,
`simp`: it rewrites with a whole list of rules, again and again, until none applies any more, and it
computes with numbers.

Which rules are in the list? In the inventory they now carry the mark *simp*; a few simple ones are
always there, such as `zero_add`, `add_zero`, `mul_one` and `true && b = b`. Not in the list are
rules like `bool_ext`, `map_true`, `mass_not` or `add_comm`: they change what you prove, or could go
on forever, and you apply them yourself. `simp [h]` puts a rule `h` into the list for this one call.
:::

:::proofde
Bisher jede Regel von Hand, eine nach der anderen. Ab jetzt stecken wir die einfachen in den
Simplifier, `simp`: Er schreibt mit einer ganzen Liste von Regeln um, immer wieder, bis keine mehr
passt, und er rechnet mit Zahlen.

Welche Regeln stehen in der Liste? Im Inventar tragen sie jetzt die Marke *simp*; ein paar einfache
sind immer dabei, etwa `zero_add`, `add_zero`, `mul_one` und `true && b = b`. Nicht in der Liste
sind Regeln wie `bool_ext`, `map_true`, `mass_not` oder `add_comm`: Sie ändern, was du beweist, oder
könnten endlos laufen, und du wendest sie selbst an. `simp [h]` nimmt eine Regel `h` für diesen
einen Aufruf in die Liste auf.
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

::::circuit (height := "440") (inputs := "x y") (gates := "and, or, not") (coins := "p p") (target := "bool true:p^2 false:1-p^2") (context := "Lean/Rules.lean") (proof := "(p q : I) : (do let x ← coin p; let y ← coin q; pure (x && y)) = coin (p * q)") (lemma := "coin_and") (new := "mass_mul") (play := "a=and; x>a.0; y>a.1; a>out") (uses := "bool_ext, bind_true, mass_mul, bind_false")
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

Compare the masses at `true`; every draw splits into its two ways (`bind_true`). One new rule:
`mass_mul : ↑(p * q) = ↑p * ↑q`, the product `p * q` in $`[0, 1]` as a mass. It carries no mark
simp: `simp [h]` takes a rule `h` along for one call.
:::

:::proofde
Dein Schaltplan, von oben nach unten gelesen, ist ein `do`-Block: `let x ← coin p` wirft eine Münze
und nennt ihr Ergebnis `x`, und `pure` am Ende ist das Ergebnis. Jedes `←` ist ein neuer Wurf,
unabhängig von den anderen. Beweise es für zwei Münzen `p` und `q` (auf dem Spielfeld waren beide
`p`): beide `true` mit Wahrscheinlichkeit $`p \cdot q`. Es wird dein Lemma `coin_and`, die
Unabhängigkeit selbst.

Vergleiche die Massen bei `true`; jeder Zug teilt sich in seine zwei Wege (`bind_true`). Eine neue
Regel: `mass_mul : ↑(p * q) = ↑p * ↑q`, das Produkt `p * q` in $`[0, 1]` als Masse. Sie trägt keine
Marke simp: `simp [h]` nimmt eine Regel `h` für einen Aufruf mit.
:::
:::solution
```
apply bool_ext
rw [bind_true, bind_true, bind_true]
simp [mass_mul]
```
:::
::::

::::leanonly (proof := "(a b : ℝ≥0∞) : a * b + b * a = 2 * a * b") (new := "ring") (uses := "-")
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

::::circuit (inputs := "x y") (gates := "and, or, not") (coins := "p p") (target := "bool true:2p(1-p) false:p^2+(1-p)^2") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure ((x || y) && !(x && y))) true = (2 * ↑p * ↑(σ p) : ℝ≥0∞)") (play := "a=or; b=and; c=not; d=and; x>a.0; y>a.1; x>b.0; y>b.1; b>c.0; a>d.0; c>d.1; d>out") (uses := "bind_true, bind_false")
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
::::
