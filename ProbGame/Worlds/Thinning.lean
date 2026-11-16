import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Thinning" =>

%%%
htmlSplit := .never
%%%

:::en
A coin is *thinned* when each `true` is kept only with probability $`q`, decided by a second coin. Thinned, a coin stays a coin, a geometric distribution stays geometric, and a binomial distribution stays binomial.
:::

:::de
Eine Münze wird *ausgedünnt*, wenn jedes `true` nur mit Wahrscheinlichkeit $`q` behalten wird; eine zweite Münze entscheidet. Ausgedünnt bleibt eine Münze eine Münze, eine geometrische Verteilung geometrisch und eine Binomialverteilung binomial.
:::

::::leanonly (proof := "(p q : I) : (do let x ← coin p; bif x then coin q else pure false) = coin ⟦p * q⟧") (lemma := "coin_thin") (group := "chance.count") (uses := "bool_ext, bind_true, mass_mul, bind_false")
:::en
*Keeping with probability q.* A coin `p` is thrown; a `true` is kept with probability $`q` (a second coin `q` decides), a `false` stays `false`. What is left is again a coin: the coin is *thinned*. With which probability does it show `true`? Fill the gap, then prove it.
:::

:::de
*Behalten mit Wahrscheinlichkeit q.* Eine Münze `p` wird geworfen; ein `true` wird mit Wahrscheinlichkeit $`q` behalten (eine zweite Münze `q` entscheidet), ein `false` bleibt `false`. Übrig bleibt wieder eine Münze: Die Münze wird *ausgedünnt*. Mit welcher Wahrscheinlichkeit zeigt sie `true`? Füll die Lücke, dann beweise es.
:::

:::proofen
Two distributions on `Bool` are the same when their masses at `true` are: `apply bool_ext`. Then `bind_true` from *Building with Coins* splits by the first coin; `norm_num` computes the rest (the masses of the coins, the `bif`), down to a product of masses: that is `mass_mul`.

*Tip.* `apply bool_ext`, `rw [bind_true]`, `norm_num`, `rw [mass_mul]`.
:::

:::proofde
Zwei Verteilungen auf `Bool` sind gleich, wenn ihre Massen bei `true` gleich sind: `apply bool_ext`. Dann teilt `bind_true` aus *Bauen mit Münzen* nach der ersten Münze; `norm_num` rechnet den Rest aus (die Massen der Münzen, die `bif`), bis ein Produkt von Massen dasteht: Das ist `mass_mul`.

*Tipp.* `apply bool_ext`, `rw [bind_true]`, `norm_num`, `rw [mass_mul]`.
:::
:::solution
```
apply bool_ext
rw [bind_true]
norm_num
rw [mass_mul]
```
:::
::::

::::leanonly (proof := "(p q : I) : (do let x ← coin p; bif x then coin q else pure false) = (do let x ← coin q; bif x then coin p else pure false)") (group := "chance.count") (uses := "coin_thin, mul_comm")
:::en
*Which first?* First `p`, then `q`, or first `q`, then `p`: the same coin.
:::

:::de
*Was zuerst?* Erst `p`, dann `q`, oder erst `q`, dann `p`: dieselbe Münze.
:::

:::proofen
Your lemma on both sides, then `mul_comm : a * b = b * a`.

*Tip.* `rw [coin_thin, coin_thin, mul_comm]`.
:::

:::proofde
Dein Lemma auf beiden Seiten, dann `mul_comm : a * b = b * a`.

*Tipp.* `rw [coin_thin, coin_thin, mul_comm]`.
:::
:::solution
```
rw [coin_thin, coin_thin, mul_comm]
```
:::
::::

::::circuit (route := "count") (inputs := "x y z") (gates := "") (coins := "p ?|? ?|?") (target := "bernoulli p^3") (start := "x>y.0; y>z.0; z>out") (context := "Lean/Rules.lean") (proof := "(p q r : I) : (do let x ← coin p; let y ← (bif x then coin q else pure false); bif y then coin r else pure false) = coin ⟦p * q * r⟧") (play := "y.T=p; y.F=0; z.T=p; z.F=0") (uses := "bind_assoc, coin_thin")
:::en
*Thinning twice.* Thinned with $`q`, and the rest thinned again with $`r`.

On the board all three coins are `p`: a coin `p`, thinned with `p`, and thinned with `p` again. Fill the fields of the two coins that wait.
:::

:::de
*Zweimal ausdünnen.* Mit $`q` ausgedünnt, und der Rest noch einmal mit $`r`.

Auf dem Spielfeld sind alle drei Münzen `p`: eine Münze `p`, mit `p` ausgedünnt und noch einmal mit `p` ausgedünnt. Füll die Felder der zwei Münzen, die warten.
:::

:::proofen
The first two steps are one coin, once they are a `do` block of their own: `rw [← bind_assoc]` (`bind_assoc : (do let y ← (do let x ← μ; f x); g y) = (do let x ← μ; let y ← f x; g y)`). Then your lemma, twice.

*Tip.* `rw [← bind_assoc, coin_thin, coin_thin]`.
:::

:::proofde
Die ersten zwei Schritte sind eine Münze, sobald sie ein eigener `do`-Block sind: `rw [← bind_assoc]` (`bind_assoc : (do let y ← (do let x ← μ; f x); g y) = (do let x ← μ; let y ← f x; g y)`). Dann dein Lemma, zweimal.

*Tipp.* `rw [← bind_assoc, coin_thin, coin_thin]`.
:::
:::solution
```
rw [← bind_assoc, coin_thin, coin_thin]
```
:::
::::

::::leanonly (proof := "(p q : I) : geom ⟦p * q⟧ = (do let x ← coin p; let y ← (bif x then coin q else pure false); bif y then pure 0 else (do let Y ← geom ⟦p * q⟧; pure (1 + Y)))") (group := "chance.count") (uses := "bind_assoc, coin_thin, geom_first")
:::en
*Waiting for a kept true.* Throw a coin `p` again and again; each `true` is kept with probability $`q` (a coin `q` decides). How many throws before the first `true` that is kept? Each throw, thinned, is a coin again: so the waiting is geometric, with which parameter? On the right: one thinned throw; on `true` it is $`0`, else start again and add one.
:::

:::de
*Warten auf ein behaltenes true.* Wirf eine Münze `p` immer wieder; jedes `true` wird mit Wahrscheinlichkeit $`q` behalten (eine Münze `q` entscheidet). Wie viele Würfe vor dem ersten behaltenen `true`? Jeder Wurf ist, ausgedünnt, wieder eine Münze: Also ist das Warten geometrisch, mit welchem Parameter? Rechts: ein ausgedünnter Wurf; bei `true` ist es $`0`, sonst fang von vorne an und zähl eins dazu.
:::

:::proofen
The first two steps on the right are a thinned coin, once they are a `do` block of their own: `rw [← bind_assoc, coin_thin]`. What stands then is the boss of *Geometric*: `exact geom_first _` (Lean finds the parameter).

*Tip.* `rw [← bind_assoc, coin_thin]`, `exact geom_first _`.
:::

:::proofde
Die ersten zwei Schritte rechts sind eine ausgedünnte Münze, sobald sie ein eigener `do`-Block sind: `rw [← bind_assoc, coin_thin]`. Was dann dasteht, ist der Endgegner aus *Geometrisch*: `exact geom_first _` (Lean findet den Parameter).

*Tipp.* `rw [← bind_assoc, coin_thin]`, `exact geom_first _`.
:::
:::solution
```
rw [← bind_assoc, coin_thin]
exact geom_first _
```
:::
::::

::::circuit (height := "640") (route := "count") (inputs := "x y") (gates := "toNat") (coins := "p ?|?") (target := "nat 0:1-p^2 1:p^2") (start := "x>y.0") (context := "Lean/Rules.lean") (proof := "(p q : I) : (do let C ← coin p; binom q C.toNat) = (do let B ← coin ⟦p * q⟧; pure B.toNat)") (lemma := "coin_bind_binom") (play := "y.T=p; y.F=0; a=toNat; y>a.0; a>out") (uses := "coin_thin, bind_assoc, binom_zero, binom_succ")
:::en
*Thinning, counted.* A coin `p`, and then as many coins `q` as it shows (one or none), counted: that is your thinned coin from the first level, counted.

On the board with `q = p`: the coin `p`, thinned by a coin that waits, then counted.
:::

:::de
*Ausdünnen, gezählt.* Eine Münze `p`, und dann so viele Münzen `q`, wie sie zeigt (eine oder keine), gezählt: Das ist deine ausgedünnte Münze aus dem ersten Level, gezählt.

Auf dem Spielfeld mit `q = p`: die Münze `p`, ausgedünnt durch eine Münze, die wartet, dann gezählt.
:::

:::proofen
`rw [← coin_thin]` writes the coin on the right as a thinned coin. Then both sides start with `coin p`: `congr 1`, `funext x`, `cases x`.

*Tip.* `rw [← coin_thin]`, `simp only [bind_assoc]`, `congr 1`, `funext x`, `cases x`; at `false`: `norm_num [binom_zero]`; at `true`: `norm_num [binom_succ, binom_zero]`.
:::

:::proofde
`rw [← coin_thin]` schreibt die Münze rechts als ausgedünnte Münze. Dann beginnen beide Seiten mit `coin p`: `congr 1`, `funext x`, `cases x`.

*Tipp.* `rw [← coin_thin]`, `simp only [bind_assoc]`, `congr 1`, `funext x`, `cases x`; bei `false`: `norm_num [binom_zero]`; bei `true`: `norm_num [binom_succ, binom_zero]`.
:::
:::solution
```
rw [← coin_thin]
simp only [bind_assoc]
congr 1
funext x
cases x
norm_num [binom_zero]
norm_num [binom_succ, binom_zero]
```
:::
::::

::::leanonly (proof := "(p q : I) (f : ℕ → DiscreteMeasure ℕ) : (do let C ← coin p; let U ← binom q C.toNat; f U) = (do let B ← coin (p * q); f B.toNat)") (lemma := "coin_bind_binom'") (group := "chance.count") (uses := "bind_assoc, coin_bind_binom, pure_bind, bind_pure")
:::en
*With something after it.* The same, when the `do` block goes on.
:::

:::de
*Mit etwas danach.* Dasselbe, wenn der `do`-Block weitergeht.
:::

:::proofen
Make the first two steps a block of their own, use your lemma, and split again.

*Tip.* `rw [← bind_assoc, coin_bind_binom, bind_assoc]`, `simp only [pure_bind]`.
:::

:::proofde
Mach die ersten zwei Schritte zu einem eigenen Block, benutze dein Lemma, und teile wieder.

*Tipp.* `rw [← bind_assoc, coin_bind_binom, bind_assoc]`, `simp only [pure_bind]`.
:::
:::solution
```
rw [← bind_assoc, coin_bind_binom, bind_assoc]
simp only [pure_bind]
```
:::
::::

::::circuit (height := "660") (size := "big") (route := "count") (inputs := "x y z w") (gates := "toNat, plus") (coins := "p ?|? p ?|?") (target := "nat 0:(1-p^2)^2 1:2p^2(1-p^2) 2:p^4") (start := "x>y.0; z>w.0") (context := "Lean/Rules.lean") (proof := "(p q : I) (n : ℕ) : (do let X ← binom p n; binom q X) = binom ⟦p * q⟧ n") (lemma := "binom_thin") (new := "bind_comm") (play := "y.T=p; y.F=0; w.T=p; w.F=0; a=toNat; b=toNat; c=plus; y>a.0; w>b.0; a>c.0; b>c.1; c>out") (uses := "binom_zero, pure_bind, binom_succ, bind_assoc, binom_add, bind_comm, coin_bind_binom', bind_pure")
:::en
*Boss: thinning a binomial.* Of $`n` throws with $`p`, each `true` is kept with probability $`q`. The number kept is binomial again: with which parameter?

On the board with $`n = 2` and `q = p`: two throws, each thinned, and the kept ones counted. The target is binomial with $`p^2`.
:::

:::de
*Endgegner: eine Binomialverteilung ausdünnen.* Von $`n` Würfen mit $`p` wird jedes `true` mit Wahrscheinlichkeit $`q` behalten. Die Anzahl der behaltenen ist wieder binomial: mit welchem Parameter?

Auf dem Spielfeld mit $`n = 2` und `q = p`: zwei Würfe, jeder ausgedünnt, und die behaltenen gezählt. Das Ziel ist binomial mit $`p^2`.
:::

:::proofen
Induction on $`n`. In the step, the first coin `C` and the other throws `X`: of `C.toNat + X`, keep is `binom q (C.toNat + X)`, by `binom_add` read backwards the sum of two independent parts. `bind_comm` swaps two independent draws, so that the part of the first coin comes first; then your last lemma.

*Tip.* `induction' n with n ih`; `rw [binom_zero, binom_zero, pure_bind, binom_zero]`; `rw [binom_succ, binom_succ (p * q), ← ih]`, `simp only [bind_assoc, pure_bind]`, `simp only [← binom_add]`, `simp only [bind_comm (binom p n) (binom q _)]`, `rw [coin_bind_binom']`.
:::

:::proofde
Induktion über $`n`. Im Schritt die erste Münze `C` und die anderen Würfe `X`: Von `C.toNat + X` behalten ist `binom q (C.toNat + X)`, nach `binom_add` rückwärts die Summe zweier unabhängiger Teile. `bind_comm` tauscht zwei unabhängige Ziehungen, damit der Teil der ersten Münze vorne steht; dann dein letztes Lemma.

*Tipp.* `induction' n with n ih`; `rw [binom_zero, binom_zero, pure_bind, binom_zero]`; `rw [binom_succ, binom_succ (p * q), ← ih]`, `simp only [bind_assoc, pure_bind]`, `simp only [← binom_add]`, `simp only [bind_comm (binom p n) (binom q _)]`, `rw [coin_bind_binom']`.
:::
:::solution
```
induction' n with n ih
rw [binom_zero, binom_zero, pure_bind, binom_zero]
rw [binom_succ, binom_succ (p * q), ← ih]
simp only [bind_assoc, pure_bind]
simp only [← binom_add]
simp only [bind_comm (binom p n) (binom q _)]
rw [coin_bind_binom']
```
:::
::::
