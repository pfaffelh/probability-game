import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Counting" =>

%%%
htmlSplit := .never
%%%

:::en
From coins to numbers: the gate *toNat* makes `false` into $`0` and `true` into $`1`, and *plus*
adds numbers (on blue wires). Count how many of $`n` coins show `true`: that number has the *binomial
distribution* $`B(n, p)`, in Lean `binom p n`. Its bars stand over $`0, 1, …, n`.
This world is one of two ways after *Building with Coins*; the other is *Coins that Wait*. They do
not need each other.
:::

:::proofen
`binom p n` is defined like the natural numbers of the Natural Number Game: `binom p 0` is
`pure 0` (no coin, surely no `true`), and `binom p (n + 1)` throws $`n` coins, then one more, and
adds: the rules `binom_zero` and `binom_succ`. Unfolding them gives a `do` block, and the monad laws
(`bind_assoc`, `pure_bind`) bring it into the form of the board. For all $`n` at once you need
*induction*, as in the Natural Number Game.
:::

:::de
Von Münzen zu Zahlen: Der Baustein *toNat* macht aus `false` die $`0` und aus `true` die $`1`, und
*plus* addiert Zahlen (auf blauen Leitungen). Zähle, wie viele von $`n` Münzen `true` zeigen: Diese
Zahl hat die *Binomialverteilung* $`B(n, p)`, in Lean `binom p n`. Ihre Säulen stehen über
$`0, 1, …, n`.
Diese Welt ist einer von zwei Wegen nach *Bauen mit Münzen*; der andere ist *Münzen, die warten*. Sie
brauchen einander nicht.
:::

:::proofde
`binom p n` ist definiert wie die natürlichen Zahlen im Natural Number Game: `binom p 0` ist `pure 0`
(keine Münze, sicher kein `true`), und `binom p (n + 1)` wirft $`n` Münzen, dann eine weitere, und
addiert: die Regeln `binom_zero` und `binom_succ`. Ausgewickelt ergibt das einen `do`-Block, und die
Monadengesetze (`bind_assoc`, `pure_bind`) bringen ihn in die Form des Spielfelds. Für alle $`n` auf
einmal brauchst du *Induktion*, wie im Natural Number Game.
:::

::::circuit (route := "count") (inputs := "x") (gates := "not, toNat") (coins := "p") (target := "nat 0:1-p 1:p") (context := "Lean/Rules.lean") (proof := "(p : I) : Bool.toNat <$> coin p = (fun b => if b then 1 else 0) <$> coin p") (play := "a=toNat; x>a.0; a>out")
:::en
*From sides to numbers.* `Bool.toNat` counts `true` as $`1` and `false` as $`0`: the distribution
moves to the natural numbers. This is how a coin becomes a random number.
:::

:::de
*Von Seiten zu Zahlen.* `Bool.toNat` zählt `true` als $`1` und `false` als $`0`: Die Verteilung
wandert zu den natürlichen Zahlen. So wird aus einer Münze eine Zufallszahl.
:::

:::proofen
`Bool.toNat` counts `true` as $`1` and `false` as $`0`. Both sides move the same coin, with two
maps that agree. As in *Maps*: `congr 1` reduces the goal to the two maps being equal, `funext b`
to their being equal at every `b`; then, as in *Circuits*, `cases b <;> rfl` does both cases in one
line.

*Tip.* `congr 1`, `funext b`, `cases b <;> rfl`.
:::

:::proofde
`Bool.toNat` zählt `true` als $`1` und `false` als $`0`. Beide Seiten bewegen dieselbe Münze, mit
zwei Abbildungen, die übereinstimmen. Wie in *Abbildungen*: `congr 1` führt das Ziel darauf zurück,
dass die beiden Abbildungen gleich sind, `funext b` darauf, dass sie an jeder Stelle `b` gleich sind;
dann erledigt, wie in *Schaltungen*, `cases b <;> rfl` beide Fälle in einer Zeile.

*Tipp.* `congr 1`, `funext b`, `cases b <;> rfl`.
:::
:::solution
```
congr 1
funext b
cases b <;> rfl
```
:::
::::

::::circuit (route := "count") (inputs := "x") (gates := "not, alwaysT, alwaysF, toNat") (coins := "p") (target := "pure 0") (context := "Lean/Rules.lean") (proof := "(p : I) : Bool.toNat <$> ((fun _ => false) <$> coin p) = pure 0") (play := "a=alwaysF; b=toNat; x>a.0; a>b.0; b>out")
:::en
*Surely zero.* A point mass on the numbers, however you get there.
:::

:::de
*Sicher null.* Eine Punktmasse auf den Zahlen, egal auf welchem Weg.
:::

:::proofen
As in *Surely `false`* (of *One Coin*) and *From sides to numbers*, now with a number.
:::

:::proofde
Wie in *Sicher `false`* (aus *Eine Münze*) und *Von Seiten zu Zahlen*, jetzt mit einer Zahl.
:::
:::solution
```
rw [coin_const, map_pure]
rfl
```
:::
::::

::::circuit (route := "count") (inputs := "x y") (gates := "toNat, plus, and, or, not") (coins := "p p") (target := "nat 0:(1-p)^2 1:2p(1-p) 2:p^2") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure (x.toNat + y.toNat)) = binom p 2") (new := "binom_zero, binom_succ, bind_assoc, pure_bind, add_zero") (play := "a=toNat; b=toNat; c=plus; x>a.0; y>b.0; a>c.0; b>c.1; c>out")
:::en
*The number of `true`.* From coins to numbers ($`0` and $`1`), and add them: the binomial distribution $`B(2, p)`.
:::

:::de
*Die Anzahl `true`.* Von Münzen zu Zahlen ($`0` und $`1`), und addieren: die Binomialverteilung $`B(2, p)`.
:::

:::proofen
The binomial distribution `binom p n` is defined as the natural numbers in the Natural Number Game:
by zero and successor. `binom_zero : binom p 0 = pure 0`: no throw, no `true`.
`binom_succ : binom p (n + 1) = do let X ← coin p; let Y ← binom p n; pure (X.toNat + Y)`: one throw
more. To clean up `do` blocks, two new rules: `bind_assoc` (a `do` block in a `do` block is one `do`
block: `(do let y ← (do let x ← μ; f x); g y) = (do let x ← μ; let y ← f x; g y)`) and
`pure_bind : (do let x ← pure a; f x) = f a` (drawing from a point mass `pure a` always gives `a`);
and `add_zero : n + 0 = n`.

*Tip.* `rw [binom_succ, binom_succ, binom_zero]`, then `simp only [bind_assoc, pure_bind, add_zero]`.
:::

:::proofde
Die Binomialverteilung `binom p n` ist definiert wie die natürlichen Zahlen im Natural Number Game:
durch Null und Nachfolger. `binom_zero : binom p 0 = pure 0`: kein Wurf, kein `true`.
`binom_succ : binom p (n + 1) = do let X ← coin p; let Y ← binom p n; pure (X.toNat + Y)`: ein Wurf
mehr. Zum Aufräumen von `do`-Blöcken zwei neue Regeln: `bind_assoc` (ein `do`-Block in einem
`do`-Block ist ein `do`-Block: `(do let y ← (do let x ← μ; f x); g y) = (do let x ← μ; let y ← f x; g y)`)
und `pure_bind : (do let x ← pure a; f x) = f a` (aus einer Punktmasse `pure a` zieht man immer `a`);
und `add_zero : n + 0 = n`.

*Tipp.* `rw [binom_succ, binom_succ, binom_zero]`, dann `simp only [bind_assoc, pure_bind, add_zero]`.
:::
:::solution
```
rw [binom_succ, binom_succ, binom_zero]
simp only [bind_assoc, pure_bind, add_zero]
```
:::
::::

::::circuit (route := "count") (size := "big") (inputs := "x y z") (gates := "toNat, plus") (coins := "p p p") (target := "nat 0:(1-p)^3 1:3p(1-p)^2 2:3p^2(1-p) 3:p^3") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; let z ← coin p; pure (x.toNat + y.toNat + z.toNat)) = binom p 3") (new := "add_assoc") (play := "a=toNat; b=toNat; c=toNat; d=plus; e=plus; x>a.0; y>b.0; z>c.0; a>d.0; b>d.1; d>e.0; c>e.1; e>out")
:::en
*Three coins.* Count the `true`s among three coins. Throw $`n` coins and count how often `true`
comes up: that is the *binomial distribution* $`B(n, p)`, with
$`P(k) = \binom{n}{k} p^k (1 - p)^{n - k}`. In the next levels, $`B(2, p)` comes already built.
:::

:::de
*Drei Münzen.* Zähle die `true` unter drei Münzen. Wirf $`n` Münzen und zähle, wie oft `true`
kommt: Das ist die *Binomialverteilung* $`B(n, p)`, mit $`P(k) = \binom{n}{k} p^k (1 - p)^{n - k}`.
In den nächsten Leveln kommt $`B(2, p)` schon gebaut.
:::

:::proofen
Three throws are `binom p 3`. New: `add_assoc : a + b + c = a + (b + c)`.

*Tip.* As in *The number of `true`*, and `add_assoc` in the `simp only`.
:::

:::proofde
Drei Würfe sind `binom p 3`. Neu: `add_assoc : a + b + c = a + (b + c)`.

*Tipp.* Wie in *Die Anzahl `true`*, und `add_assoc` im `simp only`.
:::
:::solution
```
rw [binom_succ, binom_succ, binom_succ, binom_zero]
simp only [bind_assoc, pure_bind, add_zero, add_assoc]
```
:::
::::

::::circuit (route := "count") (inputs := "x y z") (gates := "toNat, plus") (coins := "p p p") (target := "nat 0:(1-p)^3 1:3p(1-p)^2 2:3p^2(1-p) 3:p^3") (start := "a=toNat@120,160; b=toNat@240,160; c=plus@180,270; x>a.0; y>b.0; a>c.0; b>c.1") (context := "Lean/Rules.lean") (proof := "(p : I) (n : ℕ) : (do let X ← binom p n; let Y ← coin p; pure (X + Y.toNat)) = binom p (n + 1)") (lemma := "binom_succ'") (new := "induction'") (play := "d=toNat; e=plus; z>d.0; c>e.0; d>e.1; e>out")
:::en
*A new building block.* $`B(2, p)` is already built: the two coins on the left, counted and added
(it stays). Add one more coin `z`: one more throw, one more chance to count, and $`B(3, p)` comes out.
:::

:::de
*Ein neuer Baustein.* $`B(2, p)` ist schon gebaut: die zwei Münzen links, gezählt und addiert (das
bleibt). Nimm eine weitere Münze `z` dazu: ein Wurf mehr, eine Chance mehr zu zählen, und $`B(3, p)`
kommt heraus.
:::

:::proofen
`binom_succ` throws the new coin first; here it comes last, for every `n`. That needs *induction*,
as in the Natural Number Game: `induction' n with n ih` leaves two goals, one after the other: the
case $`0`, and the case $`n + 1`, with the hypothesis `ih` for $`n`. Rules can be given their
arguments: `binom_succ p n` is the rule for this `n` only. New: `zero_add : 0 + n = n`. The lemma is
called `binom_succ'`.

*Tip.* Case $`0`: `rw [binom_zero, binom_succ, binom_zero]`, `simp only [pure_bind, zero_add, add_zero]`.
Case $`n + 1`: `rw [binom_succ p n, binom_succ p (n + 1), ← ih]`, `simp only [bind_assoc, pure_bind, add_assoc]`.
:::

:::proofde
`binom_succ` wirft die neue Münze zuerst; hier kommt sie zuletzt, für jedes `n`. Dafür braucht es
*Induktion*, wie im Natural Number Game: `induction' n with n ih` lässt zwei Ziele, eines nach dem
anderen: den Fall $`0`, und den Fall $`n + 1`, mit der Annahme `ih` für $`n`. Regeln kann man ihre
Argumente mitgeben: `binom_succ p n` ist die Regel nur für dieses `n`. Neu: `zero_add : 0 + n = n`.
Das Lemma heißt `binom_succ'`.

*Tipp.* Fall $`0`: `rw [binom_zero, binom_succ, binom_zero]`, `simp only [pure_bind, zero_add, add_zero]`.
Fall $`n + 1`: `rw [binom_succ p n, binom_succ p (n + 1), ← ih]`, `simp only [bind_assoc, pure_bind, add_assoc]`.
:::
:::solution
```
induction' n with n ih
rw [binom_zero, binom_succ, binom_zero]
simp only [pure_bind, zero_add, add_zero]
rw [binom_succ p n, binom_succ p (n + 1), ← ih]
simp only [bind_assoc, pure_bind, add_assoc]
```
:::
::::

::::circuit (route := "count") (inputs := "x y z w") (gates := "plus") (coins := "p p p p") (target := "nat 0:(1-p)^4 1:4p(1-p)^3 2:6p^2(1-p)^2 3:4p^3(1-p) 4:p^4") (start := "a=toNat@62,150; b=toNat@176,150; c=plus@119,255; d=toNat@304,150; e=toNat@418,150; f=plus@361,255; x>a.0; y>b.0; a>c.0; b>c.1; z>d.0; w>e.0; d>f.0; e>f.1") (context := "Lean/Rules.lean") (proof := "(p : I) (n m : ℕ) : (do let X ← binom p n; let Y ← binom p m; pure (X + Y)) = binom p (n + m)") (lemma := "binom_add") (new := "bind_pure") (play := "g=plus; c>g.0; f>g.1; g>out")
:::en
*$`B(2, p) * B(2, p) = B(4, p)`.* Two independent binomials, both already built: add them. The sum
of independent random numbers has the *convolution* $`*` of their distributions as its distribution.
:::

:::de
*$`B(2, p) * B(2, p) = B(4, p)`.* Zwei unabhängige Binomialverteilungen, beide schon gebaut: Addiere
sie. Die Summe unabhängiger Zufallszahlen hat die *Faltung* $`*` ihrer Verteilungen als Verteilung.
:::

:::proofen
*For all $`n` and $`m`.* On the board it was $`B(2, p) * B(2, p) = B(4, p)`; here it is for all $`n` and $`m`: the
sum of independent binomials is binomial. A new rule: to draw and give back what was drawn changes
nothing, `bind_pure : (μ >>= fun x => pure x) = μ`. (In a `do` block, Lean shortens
`let x ← μ; pure x` to `μ` at once; so the rule is written with `>>=`.)

*Tip.* Induction on `m`. Case $`0`: `rw [binom_zero]`, `simp only [pure_bind, add_zero, bind_pure]`.
Case $`m + 1`: write `binom p (m + 1)` with `← binom_succ' p m`, then `n + (m + 1)` as
`n + m + 1` (`← add_assoc`) and that again with `← binom_succ' p (n + m)`; now `← ih`, and clean up
with `simp only [bind_assoc, pure_bind, add_assoc]`.
:::

:::proofde
*Für alle $`n` und $`m`.* Auf dem Spielfeld war es $`B(2, p) * B(2, p) = B(4, p)`; hier gilt es für alle $`n`
und $`m`: Die Summe unabhängiger Binomialverteilungen ist binomial. Eine neue Regel: Ziehen und das
Gezogene zurückgeben ändert nichts, `bind_pure : (μ >>= fun x => pure x) = μ`. (In einem `do`-Block
kürzt Lean `let x ← μ; pure x` sofort zu `μ`; deshalb steht die Regel mit `>>=`.)

*Tipp.* Induktion nach `m`. Fall $`0`: `rw [binom_zero]`, `simp only [pure_bind, add_zero, bind_pure]`.
Fall $`m + 1`: schreibe `binom p (m + 1)` mit `← binom_succ' p m` um, dann `n + (m + 1)` als
`n + m + 1` (`← add_assoc`) und das wieder mit `← binom_succ' p (n + m)`; jetzt `← ih`, und räume auf
mit `simp only [bind_assoc, pure_bind, add_assoc]`.
:::
:::solution
```
induction' m with m ih
rw [binom_zero]
simp only [pure_bind, add_zero, bind_pure]
rw [← binom_succ' p m, ← add_assoc, ← binom_succ' p (n + m), ← ih]
simp only [bind_assoc, pure_bind, add_assoc]
```
:::
::::

::::circuit (route := "count") (size := "big") (inputs := "x y z") (gates := "and, or") (coins := "p p p") (target := "bool true:3p^2-2p^3 false:1-3p^2+2p^3") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; let z ← coin p; pure ((x && y) || (x && z) || (y && z))) = (fun n => decide (2 ≤ n)) <$> binom p 3") (play := "a=and; b=and; c=and; d=or; e=or; x>a.0; y>a.1; x>b.0; z>b.1; y>c.0; z>c.1; a>d.0; b>d.1; d>e.0; c>e.1; e>out")
:::en
*Boss: the majority of three.* `true` when at least two of three coins show `true`. Each coin has to
go into two functions.
:::

:::de
*Boss: die Mehrheit von dreien.* `true`, wenn mindestens zwei von drei Münzen `true` zeigen. Jede Münze
muss in zwei Funktionen gehen.
:::

:::proofen
*Boss.* The majority of three is: at least two `true`, out of three throws. `decide (2 ≤ n)` is
`true` when $`2 \le n`. Everything of this world at once.

*Tip.* Unfold `binom p 3` with `binom_succ` (three times) and `binom_zero`; clean up with
`simp only [map_bind, bind_assoc, pure_bind, map_pure, add_zero]`; then go under the three throws
and look at all eight cases.
:::

:::proofde
*Endgegner.* Die Mehrheit von dreien heißt: mindestens zweimal `true`, bei drei Würfen.
`decide (2 ≤ n)` ist `true`, wenn $`2 \le n`. Alles aus dieser Welt auf einmal.

*Tipp.* Wickle `binom p 3` mit `binom_succ` (dreimal) und `binom_zero` aus; räume auf mit
`simp only [map_bind, bind_assoc, pure_bind, map_pure, add_zero]`; dann geh unter die drei Würfe und
sieh dir alle acht Fälle an.
:::
:::solution
```
rw [binom_succ, binom_succ, binom_succ, binom_zero]
simp only [map_bind, bind_assoc, pure_bind, map_pure, add_zero]
congr 1
funext x
congr 1
funext y
congr 1
funext z
cases x <;> cases y <;> cases z <;> rfl
```
:::
::::
