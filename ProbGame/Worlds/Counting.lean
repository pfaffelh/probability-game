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
This world is one of two ways after *Laws of `do`*; the other is *Multi-Stage Experiments*. They do
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
Diese Welt ist einer von zwei Wegen nach *Gesetze von `do`*; der andere ist *Mehrstufige Experimente*. Sie
brauchen einander nicht.
:::

:::proofde
`binom p n` ist definiert wie die natürlichen Zahlen im Natural Number Game: `binom p 0` ist `pure 0`
(keine Münze, sicher kein `true`), und `binom p (n + 1)` wirft $`n` Münzen, dann eine weitere, und
addiert: die Regeln `binom_zero` und `binom_succ`. Ausgewickelt ergibt das einen `do`-Block, und die
Monadengesetze (`bind_assoc`, `pure_bind`) bringen ihn in die Form des Spielfelds. Für alle $`n` auf
einmal brauchst du *Induktion*, wie im Natural Number Game.
:::

::::circuit (height := "440") (route := "count") (inputs := "x") (gates := "not, toNat") (coins := "p") (target := "nat 0:1-p 1:p") (context := "Lean/Rules.lean") (proof := "(p : I) : (coin p).map Bool.toNat = (coin p).map (fun b => if b then 1 else 0)") (play := "a=toNat; x>a.0; a>out") (uses := "-")
:::en
*From sides to numbers.* `Bool.toNat` counts `true` as $`1` and `false` as $`0`: the distribution
moves to the natural numbers. This is how a coin becomes a random number.
:::

:::de
*Von Seiten zu Zahlen.* `Bool.toNat` zählt `true` als $`1` und `false` als $`0`: Die Verteilung
wandert zu den natürlichen Zahlen. So wird aus einer Münze eine Zufallszahl.
:::

:::proofen
`Bool.toNat` counts `true` as $`1` and `false` as $`0`. Both sides move the same coin, with two maps
that agree: `congr`, as in *Laws of `do`*.
:::

:::proofde
`Bool.toNat` zählt `true` als $`1` und `false` als $`0`. Beide Seiten bewegen dieselbe Münze, mit
zwei Abbildungen, die übereinstimmen: `congr`, wie in *Gesetze von `do`*.
:::
:::solution
```
congr
ext b
cases b <;> rfl
```
:::
::::

::::circuit (height := "540") (route := "count") (inputs := "x") (gates := "not, alwaysT, alwaysF, toNat") (coins := "p") (target := "pure 0") (context := "Lean/Rules.lean") (proof := "(p : I) : ((coin p).map (fun _ => false)).map Bool.toNat = pure 0") (play := "a=alwaysF; b=toNat; x>a.0; a>b.0; b>out") (uses := "coin_const, map_pure")
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

:::::leanonly (proof := "(p : I) : binom p 0 = pure 0") (lemma := "binom_zero") (group := "chance.count") (uses := "-")
::::hint (anchor := "statement")
:::en
`binom p n`: the number of `true` in $`n` throws of `coin p`. Lean defines it by recursion on $`n`:

```
def binom (p : I) : ℕ → DiscreteMeasure ℕ
  | 0 => pure 0
  | n + 1 => do
    let X ← coin p
    let Y ← binom p n
    pure (X.toNat + Y)
```
:::

:::de
`binom p n`: die Anzahl der `true` in $`n` Würfen von `coin p`. Lean definiert sie durch Rekursion über $`n`:

```
def binom (p : I) : ℕ → DiscreteMeasure ℕ
  | 0 => pure 0
  | n + 1 => do
    let X ← coin p
    let Y ← binom p n
    pure (X.toNat + Y)
```
:::
::::

:::en
*No throw.* `binom p n` is the number of `true` in $`n` throws of `coin p`. With no throw it is surely $`0`.
:::

:::de
*Kein Wurf.* `binom p n` ist die Anzahl der `true` in $`n` Würfen von `coin p`. Ohne Wurf ist sie sicher $`0`.
:::

:::proofen
`binom` is defined by recursion on $`n`, as the natural numbers are (the definition is in the tip at
the statement); this is its first case, true by definition.
:::

:::proofde
`binom` ist durch Rekursion über $`n` definiert, wie die natürlichen Zahlen (die Definition steht im
Tipp an der Aussage); das ist ihr erster Fall, wahr nach Definition.
:::
:::solution
```
rfl
```
:::
:::::

:::::leanonly (proof := "(p : I) (n : ℕ) : binom p (n + 1) = (do let X ← coin p; let Y ← binom p n; pure ⟦X.toNat + Y ‖ X.toNat + Y, Y, X.toNat⟧)") (lemma := "binom_succ") (group := "chance.count") (uses := "-")
::::hint (anchor := "gap")
:::en
One coin `X`, the count `Y` of the other $`n`: what is the count of all $`n + 1`?
:::

:::de
Eine Münze `X`, die Anzahl `Y` der anderen $`n`: Was ist die Anzahl aller $`n + 1`?
:::
::::

:::en
*One throw more.* $`n + 1` throws: one coin, then $`n` throws, and the numbers added.
:::

:::de
*Ein Wurf mehr.* $`n + 1` Würfe: eine Münze, dann $`n` Würfe, und die Anzahlen addiert.
:::

:::proofen
The second case of the definition.
:::

:::proofde
Der zweite Fall der Definition.
:::
:::solution
```
rfl
```
:::
:::::

::::leanonly (proof := "(p : I) : (do let x ← (pure true : DiscreteMeasure Bool); bif x then coin p else pure false) = coin p") (new := "pure_bind") (group := "chance.count") (uses := "pure_bind, Bool.cond_true, bind_pure, Bool.cond_false")
:::en
*Drawing a sure value.* Drawing from `pure a` gives `a`, surely.
:::

:::de
*Einen sicheren Wert ziehen.* Aus `pure a` ziehen ergibt sicher `a`.
:::

:::proofen
`pure_bind : (do let x ← pure a; f x) = f a`.
:::

:::proofde
`pure_bind : (do let x ← pure a; f x) = f a`.
:::
:::solution
```
rw [pure_bind, Bool.cond_true]
```
:::
::::

::::leanonly (proof := "(p : I) : (do let y ← (do let x ← coin p; pure (!x)); pure (!y)) = (do let x ← coin p; let y ← pure (!x); pure (!y))") (new := "bind_assoc") (group := "chance.count") (uses := "bind_assoc")
:::en
*A do block in a do block.* A `do` block inside another can be written out: one step after the other.
:::

:::de
*Ein do-Block im do-Block.* Ein `do`-Block in einem anderen kann ausgeschrieben werden: ein Schritt nach dem anderen.
:::

:::proofen
`bind_assoc : (do let y ← (do let x ← μ; f x); g y) = (do let x ← μ; let y ← f x; g y)`.
:::

:::proofde
`bind_assoc : (do let y ← (do let x ← μ; f x); g y) = (do let x ← μ; let y ← f x; g y)`.
:::
:::solution
```
rw [bind_assoc]
```
:::
::::

::::leanonly (proof := "(x : Bool) : x.toNat + 0 = x.toNat") (new := "add_zero") (group := "chance.count") (uses := "add_zero, zero_add")
:::en
*Plus zero.* `x.toNat` is the number of `x`: $`1` for `true`, $`0` for `false`. Adding zero changes nothing.
:::

:::de
*Plus null.* `x.toNat` ist die Zahl von `x`: $`1` für `true`, $`0` für `false`. Null addieren ändert nichts.
:::

:::proofen
`add_zero : a + 0 = a`.
:::

:::proofde
`add_zero : a + 0 = a`.
:::
:::solution
```
rw [add_zero]
```
:::
::::

::::circuit (route := "count") (inputs := "x y") (gates := "toNat, plus, and, or, not") (coins := "p p") (target := "nat 0:(1-p)^2 1:2p(1-p) 2:p^2") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure (x.toNat + y.toNat)) = binom p 2") (play := "a=toNat; b=toNat; c=plus; x>a.0; y>b.0; a>c.0; b>c.1; c>out") (uses := "binom_succ, binom_zero, bind_assoc, pure_bind, add_zero, bind_pure, zero_add")
:::en
*The number of `true`.* From coins to numbers ($`0` and $`1`), and add them: the binomial distribution $`B(2, p)`.
:::

:::de
*Die Anzahl `true`.* Von Münzen zu Zahlen ($`0` und $`1`), und addieren: die Binomialverteilung $`B(2, p)`.
:::

:::proofen
`binom p 2`, written out by its two rules, is a `do` block in a `do` block. The rules of the last
three levels clean it up (under bound names: `simp_rw`).
:::

:::proofde
`binom p 2`, mit seinen zwei Regeln ausgeschrieben, ist ein `do`-Block in einem `do`-Block. Die
Regeln der letzten drei Level räumen ihn auf (unter gebundenen Namen: `simp_rw`).
:::
:::solution
```
rw [binom_succ, binom_succ, binom_zero]
simp_rw [bind_assoc, pure_bind, add_zero]
```
:::
::::

::::quiz (tactic := "simp [binom_succ, binom_zero, bind_assoc]") (statements := "(p : I) : binom p 2 = (do let x ← coin p; let y ← coin p; pure (x.toNat + y.toNat)) ;; (p : I) : binom p 2 = (do let x ← coin p; pure (x.toNat + x.toNat)) ;; (p : I) : binom p 1 = (do let x ← coin p; pure x.toNat) ;; (p : I) : binom p 2 = (do let x ← coin p; let y ← coin p; pure (x && y).toNat) ;; (p : I) : binom p 2 = (do let x ← coin p; let y ← coin (σ p); pure (x.toNat + y.toNat)) ;; (p : I) : binom p 3 = (do let x ← coin p; let y ← coin p; let z ← coin p; pure (x.toNat + (y.toNat + z.toNat)))") (answer := "1, 3, 6") (context := "Lean/Rules.lean") (group := "chance.count")
:::en
*Which circuits?* Which of these `do` blocks is a binomial distribution `binom p n`? The tactic
unfolds `binom` and cleans up the `do` blocks, as in the level before: `simp` with `binom_succ`,
`binom_zero` and `bind_assoc` added.
:::

:::de
*Welche Schaltungen?* Welcher dieser `do`-Blöcke ist eine Binomialverteilung `binom p n`? Die Taktik
wickelt `binom` aus und räumt die `do`-Blöcke auf, wie im Level davor: `simp`, dazu `binom_succ`,
`binom_zero` und `bind_assoc`.
:::
::::

::::leanonly (proof := "(x y z : Bool) : x.toNat + y.toNat + z.toNat = x.toNat + (y.toNat + z.toNat)") (new := "add_assoc") (group := "chance.count") (uses := "add_assoc, add_comm, add_right_comm")
:::en
*Brackets.* In a sum, the brackets can move.
:::

:::de
*Klammern.* In einer Summe können die Klammern wandern.
:::

:::proofen
`add_assoc : a + b + c = a + (b + c)` (`a + b + c` is `(a + b) + c`).
:::

:::proofde
`add_assoc : a + b + c = a + (b + c)` (`a + b + c` ist `(a + b) + c`).
:::
:::solution
```
rw [add_assoc]
```
:::
::::

::::circuit (height := "660") (route := "count") (size := "big") (inputs := "x y z") (gates := "toNat, plus") (coins := "p p p") (target := "nat 0:(1-p)^3 1:3p(1-p)^2 2:3p^2(1-p) 3:p^3") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; let z ← coin p; pure (x.toNat + y.toNat + z.toNat)) = binom p 3") (play := "a=toNat; b=toNat; c=toNat; d=plus; e=plus; x>a.0; y>b.0; z>c.0; a>d.0; b>d.1; d>e.0; c>e.1; e>out") (uses := "binom_succ, binom_zero, bind_assoc, pure_bind, add_zero, add_assoc, bind_pure, zero_add, add_comm, add_right_comm")
:::en
*Three coins.* Count the `true`s among three coins. Throw $`n` coins and count how often `true`
comes up: that is the *binomial distribution* $`B(n, p)`, with
$`P(k) = \binom{n}{k} p^k (1 - p)^{n - k}`. Later in this world, $`B(2, p)` comes already built.
:::

:::de
*Drei Münzen.* Zähle die `true` unter drei Münzen. Wirf $`n` Münzen und zähle, wie oft `true`
kommt: Das ist die *Binomialverteilung* $`B(n, p)`, mit $`P(k) = \binom{n}{k} p^k (1 - p)^{n - k}`.
Später in dieser Welt kommt $`B(2, p)` schon gebaut.
:::

:::proofen
Three throws are `binom p 3`: as for two, now with `add_assoc` as well.
:::

:::proofde
Drei Würfe sind `binom p 3`: wie bei zweien, jetzt auch mit `add_assoc`.
:::
:::solution
```
rw [binom_succ, binom_succ, binom_succ, binom_zero]
simp_rw [bind_assoc, pure_bind, add_zero, add_assoc]
```
:::
::::

::::circuit (height := "660") (route := "count") (size := "big") (inputs := "x y z") (gates := "and, or") (coins := "p p p") (target := "bool true:3p^2-2p^3 false:1-3p^2+2p^3") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; let z ← coin p; pure ((x && y) || (x && z) || (y && z))) = (binom p 3).map (fun n => decide (2 ≤ n))") (play := "a=and; b=and; c=and; d=or; e=or; x>a.0; y>a.1; x>b.0; z>b.1; y>c.0; z>c.1; a>d.0; b>d.1; d>e.0; c>e.1; e>out") (uses := "binom_succ, binom_zero, map_bind, bind_assoc, pure_bind, map_pure, add_zero, bind_map_left, bind_pure, zero_add")
:::en
*The majority of three.* `true` when at least two of three coins show `true`. Each coin has to
go into two functions.
:::

:::de
*Die Mehrheit von dreien.* `true`, wenn mindestens zwei von drei Münzen `true` zeigen. Jede Münze
muss in zwei Funktionen gehen.
:::
:::proofen
The majority is a move on the number of `true`: at least two of three. The move at the end goes into
the `do` block, with `map_bind` and `map_pure` from *Laws of `do`*. Then both sides throw the same
three coins and differ only in what they compute.
:::

:::proofde
Die Mehrheit ist ein Zug auf der Anzahl der `true`: mindestens zwei von dreien. Der Zug am Ende
wandert in den `do`-Block, mit `map_bind` und `map_pure` aus *Gesetze von `do`*. Dann werfen beide
Seiten dieselben drei Münzen und unterscheiden sich nur darin, was sie rechnen.
:::
:::solution
```
rw [binom_succ, binom_succ, binom_succ, binom_zero]
simp_rw [map_bind, bind_assoc, pure_bind, map_pure, add_zero]
congr
ext x
congr
ext y
congr
ext z
cases x <;> cases y <;> cases z <;> rfl
```
:::
::::

::::leanonly (proof := "(n : ℕ) : binom 0 n = pure 0") (lemma := "binom_never") (new := "induction', coin_zero") (group := "chance.count") (uses := "binom_zero, binom_succ, coin_zero, pure_bind, coin_one, bind_pure")
:::en
*A coin that never shows `true`.* The coin with $`p = 0` shows `false`, surely. Throw it $`n` times and count the `true`: surely $`0`, for every $`n`.
:::

:::de
*Eine Münze, die nie `true` zeigt.* Die Münze mit $`p = 0` zeigt sicher `false`. Wirf sie $`n`-mal und zähl die `true`: sicher $`0`, für jedes $`n`.
:::

:::proofen
For every $`n`: that needs *induction*, as in the Natural Number Game. The new tactic
`induction' n with n ih` leaves two goals, one after the other: the case $`0`, and the case
$`n + 1`, with the hypothesis `ih` for $`n`. The new rule `coin_zero : coin 0 = pure false` says
what the coin shows. Your result becomes the lemma `binom_never`.
:::

:::proofde
Für jedes $`n`: Dafür braucht es *Induktion*, wie im Natural Number Game. Die neue Taktik
`induction' n with n ih` lässt zwei Ziele, eines nach dem anderen: den Fall $`0`, und den Fall
$`n + 1`, mit der Annahme `ih` für $`n`. Die neue Regel `coin_zero : coin 0 = pure false` sagt, was
die Münze zeigt. Dein Ergebnis wird das Lemma `binom_never`.
:::
:::solution
```
induction' n with n ih
rw [binom_zero]
rw [binom_succ, coin_zero, pure_bind, ih, pure_bind]
rfl
```
:::
::::

::::circuit (route := "count") (inputs := "x y z") (gates := "toNat, plus") (coins := "p p p") (target := "nat 0:(1-p)^3 1:3p(1-p)^2 2:3p^2(1-p) 3:p^3") (start := "a=toNat@120,160; b=toNat@240,160; c=plus@180,270; x>a.0; y>b.0; a>c.0; b>c.1") (context := "Lean/Rules.lean") (proof := "(p : I) (n : ℕ) : (do let X ← binom p n; let Y ← coin p; pure (X + Y.toNat)) = binom p (n + 1)") (lemma := "binom_succ'") (play := "d=toNat; e=plus; z>d.0; c>e.0; d>e.1; e>out") (uses := "binom_zero, binom_succ, pure_bind, zero_add, add_zero, bind_assoc, add_assoc, bind_pure, mul_zero, add_comm, add_right_comm")
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
`binom_succ` throws the new coin first; here it comes last, for every `n`: induction, as in the
level before. Rules can be given their arguments: `binom_succ p n` is the rule for this `n` only.
The lemma is called `binom_succ'`.
:::

:::proofde
`binom_succ` wirft die neue Münze zuerst; hier kommt sie zuletzt, für jedes `n`: Induktion, wie im
Level davor. Regeln kann man ihre Argumente mitgeben: `binom_succ p n` ist die Regel nur für dieses
`n`. Das Lemma heißt `binom_succ'`.
:::
:::solution
```
induction' n with n ih
rw [binom_zero, binom_succ, binom_zero]
simp_rw [pure_bind, zero_add, add_zero]
rw [binom_succ p n, binom_succ p (n + 1), ← ih]
simp_rw [bind_assoc, pure_bind, add_assoc]
```
:::
::::

::::circuit (height := "540") (route := "count") (inputs := "x y z w") (gates := "plus") (coins := "p p p p") (target := "nat 0:(1-p)^4 1:4p(1-p)^3 2:6p^2(1-p)^2 3:4p^3(1-p) 4:p^4") (start := "a=toNat@62,150; b=toNat@176,150; c=plus@119,255; d=toNat@304,150; e=toNat@418,150; f=plus@361,255; x>a.0; y>b.0; a>c.0; b>c.1; z>d.0; w>e.0; d>f.0; e>f.1") (context := "Lean/Rules.lean") (proof := "(p : I) (n m : ℕ) : (do let X ← binom p n; let Y ← binom p m; pure (X + Y)) = binom p (n + m)") (lemma := "binom_add") (play := "g=plus; c>g.0; f>g.1; g>out") (uses := "binom_zero, pure_bind, add_zero, bind_pure, binom_succ', add_assoc, bind_assoc, binom_succ, zero_add, add_comm, add_right_comm")
:::en
*Boss: $`B(2, p) * B(2, p) = B(4, p)`.* Two independent binomials, both already built: add them. The sum
of independent random numbers has the *convolution* $`*` of their distributions as its distribution.
:::

:::de
*Endgegner: $`B(2, p) * B(2, p) = B(4, p)`.* Zwei unabhängige Binomialverteilungen, beide schon gebaut: Addiere
sie. Die Summe unabhängiger Zufallszahlen hat die *Faltung* $`*` ihrer Verteilungen als Verteilung.
:::

:::proofen
*For all $`n` and $`m`.* On the board it was $`B(2, p) * B(2, p) = B(4, p)`; here it is for all $`n` and $`m`: the
sum of independent binomials is binomial. Your result becomes the lemma `binom_add`.
:::

:::proofde
*Für alle $`n` und $`m`.* Auf dem Spielfeld war es $`B(2, p) * B(2, p) = B(4, p)`; hier gilt es für alle $`n`
und $`m`: Die Summe unabhängiger Binomialverteilungen ist binomial. Dein Ergebnis wird das Lemma `binom_add`.
:::
:::solution
```
induction' m with m ih
rw [binom_zero]
simp_rw [pure_bind, add_zero, bind_pure]
rw [← binom_succ' p m, ← add_assoc, ← binom_succ' p (n + m), ← ih]
simp_rw [bind_assoc, pure_bind, add_assoc]
```
:::
::::
