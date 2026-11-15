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

::::leanonly (proof := "(p : I) : binom p 0 = pure 0") (lemma := "binom_zero") (group := "chance.count")
:::en
*No throw.* `binom p n` is the number of `true` in $`n` throws of `coin p`. With no throw it is surely $`0`.
:::

:::de
*Kein Wurf.* `binom p n` ist die Anzahl der `true` in $`n` Würfen von `coin p`. Ohne Wurf ist sie sicher $`0`.
:::

:::proofen
`binom` is defined by recursion on $`n`, as the natural numbers are; this is its first case:

```
def binom (p : I) : ℕ → DiscreteMeasure ℕ
  | 0 => pure 0
  | n + 1 => do
    let X ← coin p
    let Y ← binom p n
    pure (X.toNat + Y)
```

*Tip.* `rfl`.
:::

:::proofde
`binom` ist durch Rekursion über $`n` definiert, wie die natürlichen Zahlen; das ist ihr erster Fall:

```
def binom (p : I) : ℕ → DiscreteMeasure ℕ
  | 0 => pure 0
  | n + 1 => do
    let X ← coin p
    let Y ← binom p n
    pure (X.toNat + Y)
```

*Tipp.* `rfl`.
:::
:::solution
```
rfl
```
:::
::::

::::leanonly (proof := "(p : I) (n : ℕ) : binom p (n + 1) = (do let X ← coin p; let Y ← binom p n; pure (X.toNat + Y))") (lemma := "binom_succ") (group := "chance.count")
:::en
*One throw more.* $`n + 1` throws: one coin, then $`n` throws, and the numbers added.
:::

:::de
*Ein Wurf mehr.* $`n + 1` Würfe: eine Münze, dann $`n` Würfe, und die Anzahlen addiert.
:::

:::proofen
The second case of the definition.

*Tip.* `rfl`.
:::

:::proofde
Der zweite Fall der Definition.

*Tipp.* `rfl`.
:::
:::solution
```
rfl
```
:::
::::

::::leanonly (proof := "(p : I) : (do let x ← (pure true : DiscreteMeasure Bool); bif x then coin p else pure false) = coin p") (new := "pure_bind") (group := "chance.count")
:::en
*Drawing a sure value.* Drawing from `pure a` gives `a`, surely.
:::

:::de
*Einen sicheren Wert ziehen.* Aus `pure a` ziehen ergibt sicher `a`.
:::

:::proofen
`pure_bind : (do let x ← pure a; f x) = f a`.

*Tip.* `rw [pure_bind, Bool.cond_true]`.
:::

:::proofde
`pure_bind : (do let x ← pure a; f x) = f a`.

*Tipp.* `rw [pure_bind, Bool.cond_true]`.
:::
:::solution
```
rw [pure_bind, Bool.cond_true]
```
:::
::::

::::leanonly (proof := "(p : I) : (do let y ← (do let x ← coin p; pure (!x)); pure (!y)) = (do let x ← coin p; let y ← pure (!x); pure (!y))") (new := "bind_assoc") (group := "chance.count")
:::en
*A do block in a do block.* A `do` block inside another can be written out: one step after the other.
:::

:::de
*Ein do-Block im do-Block.* Ein `do`-Block in einem anderen kann ausgeschrieben werden: ein Schritt nach dem anderen.
:::

:::proofen
`bind_assoc : (μ >>= f) >>= g = μ >>= fun x => f x >>= g`.

*Tip.* `rw [bind_assoc]`.
:::

:::proofde
`bind_assoc : (μ >>= f) >>= g = μ >>= fun x => f x >>= g`.

*Tipp.* `rw [bind_assoc]`.
:::
:::solution
```
rw [bind_assoc]
```
:::
::::

::::leanonly (proof := "(x : Bool) : x.toNat + 0 = x.toNat") (new := "add_zero") (group := "chance.count")
:::en
*Plus zero.* `x.toNat` is the number of `x`: $`1` for `true`, $`0` for `false`. Adding zero changes nothing.
:::

:::de
*Plus null.* `x.toNat` ist die Zahl von `x`: $`1` für `true`, $`0` für `false`. Null addieren ändert nichts.
:::

:::proofen
`add_zero : a + 0 = a`.

*Tip.* `rw [add_zero]`.
:::

:::proofde
`add_zero : a + 0 = a`.

*Tipp.* `rw [add_zero]`.
:::
:::solution
```
rw [add_zero]
```
:::
::::

::::leanonly (proof := "(x y z : Bool) : x.toNat + y.toNat + z.toNat = x.toNat + (y.toNat + z.toNat)") (new := "add_assoc") (group := "chance.count")
:::en
*Brackets.* In a sum, the brackets can move.
:::

:::de
*Klammern.* In einer Summe können die Klammern wandern.
:::

:::proofen
`add_assoc : a + b + c = a + (b + c)` (`a + b + c` is `(a + b) + c`).

*Tip.* `rw [add_assoc]`.
:::

:::proofde
`add_assoc : a + b + c = a + (b + c)` (`a + b + c` ist `(a + b) + c`).

*Tipp.* `rw [add_assoc]`.
:::
:::solution
```
rw [add_assoc]
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

::::leanonly (proof := "(p : I) : coin p >>= pure = coin p") (new := "bind_pure") (group := "chance.count")
:::en
*Drawing and giving back.* Drawing from `μ` and giving back what was drawn is `μ`.
:::

:::de
*Ziehen und zurückgeben.* Aus `μ` ziehen und das Gezogene zurückgeben ist `μ`.
:::

:::proofen
`bind_pure : μ >>= pure = μ` (`do let x ← μ; pure x` is `μ`).

*Tip.* `rw [bind_pure]`.
:::

:::proofde
`bind_pure : μ >>= pure = μ` (`do let x ← μ; pure x` ist `μ`).

*Tipp.* `rw [bind_pure]`.
:::
:::solution
```
rw [bind_pure]
```
:::
::::

::::circuit (height := "660") (route := "count") (size := "big") (inputs := "x y z") (gates := "and, or") (coins := "p p p") (target := "bool true:3p^2-2p^3 false:1-3p^2+2p^3") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; let z ← coin p; pure ((x && y) || (x && z) || (y && z))) = (fun n => decide (2 ≤ n)) <$> binom p 3") (play := "a=and; b=and; c=and; d=or; e=or; x>a.0; y>a.1; x>b.0; z>b.1; y>c.0; z>c.1; a>d.0; b>d.1; d>e.0; c>e.1; e>out")
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
