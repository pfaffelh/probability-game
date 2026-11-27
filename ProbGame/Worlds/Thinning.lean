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

::::leanonly (proof := "(p q : I) : (do let x ← coin p; bif x then coin q else pure false) = coin ⟦p * q⟧") (lemma := "coin_thin") (group := "chance.count") (uses := "bool_ext, bind_true, mass_mul, bind_false, apply, rw, simp")
:::en
*Keeping with probability q.* A coin `p` is thrown; a `true` is kept with probability $`q` (a second coin `q` decides), a `false` stays `false`. What is left is again a coin: the coin is *thinned*. With which probability does it show `true`? Fill the gap, then prove it.
:::

:::de
*Behalten mit Wahrscheinlichkeit q.* Eine Münze `p` wird geworfen; ein `true` wird mit Wahrscheinlichkeit $`q` behalten (eine zweite Münze `q` entscheidet), ein `false` bleibt `false`. Übrig bleibt wieder eine Münze: Die Münze wird *ausgedünnt*. Mit welcher Wahrscheinlichkeit zeigt sie `true`? Füll die Lücke, dann beweise es.
:::

:::proofen
Compare the masses at `true`, split by the first coin, and compute, down to a product of masses:
that is `mass_mul`.
:::

:::proofde
Vergleiche die Massen bei `true`, teile nach der ersten Münze, und rechne, bis ein Produkt von
Massen dasteht: Das ist `mass_mul`.
:::
:::solution
```
apply bool_ext
rw [bind_true]
simp
rw [mass_mul]
```
:::
::::

::::leanonly (proof := "(p q : I) : (do let x ← coin p; bif x then coin q else pure false) = (do let x ← coin q; bif x then coin p else pure false)") (group := "chance.count") (uses := "coin_thin, mul_comm, rw")
:::en
*Which first?* First `p`, then `q`, or first `q`, then `p`: the same coin.
:::

:::de
*Was zuerst?* Erst `p`, dann `q`, oder erst `q`, dann `p`: dieselbe Münze.
:::

:::proofen
Your lemma on both sides, then `mul_comm : a * b = b * a`.
:::

:::proofde
Dein Lemma auf beiden Seiten, dann `mul_comm : a * b = b * a`.
:::
:::solution
```
rw [coin_thin, coin_thin, mul_comm]
```
:::
::::

::::circuit (route := "count") (inputs := "x y z") (gates := "") (coins := "p ?|? ?|?") (target := "bernoulli p^3") (start := "x>y.0; y>z.0; z>out") (context := "Lean/Rules.lean") (proof := "(p q r : I) : (do let x ← coin p; let y ← (bif x then coin q else pure false); bif y then coin r else pure false) = coin (p * q * r)") (play := "y.T=p; y.F=0; z.T=p; z.F=0") (uses := "bind_assoc, coin_thin, rw")
:::en
*Thinning twice.* Thinned with $`q`, and the rest thinned again with $`r`.

On the board all three coins are `p`: a coin `p`, thinned with `p`, and thinned with `p` again. Fill the fields of the coins of the second and the third stage.
:::

:::de
*Zweimal ausdünnen.* Mit $`q` ausgedünnt, und der Rest noch einmal mit $`r`.

Auf dem Spielfeld sind alle drei Münzen `p`: eine Münze `p`, mit `p` ausgedünnt und noch einmal mit `p` ausgedünnt. Füll die Felder der Münzen der zweiten und der dritten Stufe.
:::

:::proofen
The first two steps are one coin, once they are a `do` block of their own:
`bind_assoc : (do let y ← (do let x ← μ; f x); g y) = (do let x ← μ; let y ← f x; g y)`, backwards.
:::

:::proofde
Die ersten zwei Schritte sind eine Münze, sobald sie ein eigener `do`-Block sind:
`bind_assoc : (do let y ← (do let x ← μ; f x); g y) = (do let x ← μ; let y ← f x; g y)`, rückwärts.
:::
:::solution
```
rw [← bind_assoc, coin_thin, coin_thin]
```
:::
::::

::::leanonly (proof := "(p q : I) : geom ⟦p * q⟧ = (do let x ← coin p; let y ← (bif x then coin q else pure false); bif y then pure 0 else (do let Y ← geom ⟦p * q⟧; pure (1 + Y)))") (group := "chance.count") (uses := "bind_assoc, coin_thin, geom_first, exact, rw")
:::en
*Waiting for a kept true.* Throw a coin `p` again and again; each `true` is kept with probability $`q` (a coin `q` decides). How many throws before the first `true` that is kept? Each throw, thinned, is a coin again: so the waiting is geometric, with which parameter? On the right: one thinned throw; on `true` it is $`0`, else start again and add one.
:::

:::de
*Warten auf ein behaltenes true.* Wirf eine Münze `p` immer wieder; jedes `true` wird mit Wahrscheinlichkeit $`q` behalten (eine Münze `q` entscheidet). Wie viele Würfe vor dem ersten behaltenen `true`? Jeder Wurf ist, ausgedünnt, wieder eine Münze: Also ist das Warten geometrisch, mit welchem Parameter? Rechts: ein ausgedünnter Wurf; bei `true` ist es $`0`, sonst fang von vorne an und zähl eins dazu.
:::

:::proofen
The first two steps on the right are a thinned coin, once they are a `do` block of their own. What
stands then is the boss of *Geometric*, `geom_first`; a parameter Lean is to find itself is written
`_`.
:::

:::proofde
Die ersten zwei Schritte rechts sind eine ausgedünnte Münze, sobald sie ein eigener `do`-Block sind.
Was dann dasteht, ist der Endgegner aus *Geometrisch*, `geom_first`; einen Parameter, den Lean
selbst finden soll, schreibt man `_`.
:::
:::solution
```
rw [← bind_assoc, coin_thin]
exact geom_first _
```
:::
::::

::::circuit (height := "640") (route := "count") (inputs := "x y") (gates := "toNat") (coins := "p ?|?") (target := "nat 0:1-p^2 1:p^2") (start := "x>y.0") (context := "Lean/Rules.lean") (proof := "(p q : I) : (do let C ← coin p; binom q C.toNat) = (do let B ← coin (p * q); pure B.toNat)") (lemma := "coin_bind_binom") (play := "y.T=p; y.F=0; a=toNat; y>a.0; a>out") (uses := "coin_thin, bind_assoc, binom_zero, binom_succ, cases, congr, ext, rw, simp, simp_rw")
:::en
*Thinning, counted.* A coin `p`, and then as many coins `q` as it shows (one or none), counted: that is your thinned coin from the first level, counted.

On the board with `q = p`: the coin `p`, thinned by a coin of a second stage, then counted.
:::

:::de
*Ausdünnen, gezählt.* Eine Münze `p`, und dann so viele Münzen `q`, wie sie zeigt (eine oder keine), gezählt: Das ist deine ausgedünnte Münze aus dem ersten Level, gezählt.

Auf dem Spielfeld mit `q = p`: die Münze `p`, ausgedünnt durch eine Münze einer zweiten Stufe, dann gezählt.
:::

:::proofen
Write the coin on the right as a thinned coin (`coin_thin`, backwards). Then both sides start with
`coin p`.
:::

:::proofde
Schreib die Münze rechts als ausgedünnte Münze (`coin_thin`, rückwärts). Dann beginnen beide Seiten
mit `coin p`.
:::
:::solution
```
rw [← coin_thin]
simp_rw [bind_assoc]
congr
ext x
cases x
simp [binom_zero]
simp [binom_succ, binom_zero]
```
:::
::::

::::leanonly (proof := "(p q : I) (f : ℕ → DiscreteMeasure ℕ) : (do let C ← coin p; let U ← binom q C.toNat; f U) = (do let B ← coin (p * q); f B.toNat)") (lemma := "coin_bind_binom'") (group := "chance.count") (uses := "bind_assoc, coin_bind_binom, pure_bind, bind_pure, rw, simp_rw")
:::en
*With something after it.* The same, when the `do` block goes on.
:::

:::de
*Mit etwas danach.* Dasselbe, wenn der `do`-Block weitergeht.
:::

:::proofen
Make the first two steps a block of their own, use your lemma, and split again.
:::

:::proofde
Mach die ersten zwei Schritte zu einem eigenen Block, benutze dein Lemma, und teile wieder.
:::
:::solution
```
rw [← bind_assoc, coin_bind_binom, bind_assoc]
simp_rw [pure_bind]
```
:::
::::

::::leanonly (proof := "(p q : I) : (do let x ← coin p; let y ← coin q; pure (x && !y)) = (do let y ← coin q; let x ← coin p; pure (x && !y))") (new := "bind_comm") (group := "chance.count") (uses := "bind_comm, rw")
:::en
*Which coin first?* Two coins, thrown independently: it does not matter which is thrown first.
:::

:::de
*Welche Münze zuerst?* Zwei Münzen, unabhängig geworfen: Es ist egal, welche zuerst geworfen wird.
:::

:::proofen
`bind_comm μ ν : (do let x ← μ; let y ← ν; f x y) = (do let y ← ν; let x ← μ; f x y)`: two independent draws, in the other order. (Independent: `ν` does not use `x`.)
:::

:::proofde
`bind_comm μ ν : (do let x ← μ; let y ← ν; f x y) = (do let y ← ν; let x ← μ; f x y)`: zwei unabhängige Ziehungen, in der anderen Reihenfolge. (Unabhängig: `ν` benutzt `x` nicht.)
:::
:::solution
```
rw [bind_comm]
```
:::
::::

::::leanonly (proof := "(p q r : I) : (do let z ← coin r; let x ← coin p; let y ← coin q; pure (z && x && !y)) = (do let z ← coin r; let y ← coin q; let x ← coin p; pure (z && x && !y))") (group := "chance.count") (uses := "bind_comm, simp_rw")
:::en
*Swapping further down.* The same two coins, but a third one is thrown before them.
:::

:::de
*Tauschen weiter unten.* Dieselben zwei Münzen, aber vor ihnen wird eine dritte geworfen.
:::

:::proofen
The two draws stand under `let z ← coin r`: there `rw` does not reach, `simp_rw` does. But `simp_rw [bind_comm]` would swap for ever, back and forth. So say which two draws: `bind_comm μ ν`
swaps only where `μ` is drawn right before `ν`. (A part Lean is to find itself is written `_`.)
:::

:::proofde
Die zwei Ziehungen stehen unter `let z ← coin r`: Dorthin reicht `rw` nicht, `simp_rw` schon. Aber `simp_rw [bind_comm]` würde endlos tauschen, hin und her. Sag also, welche zwei Ziehungen:
`bind_comm μ ν` tauscht nur dort, wo `μ` direkt vor `ν` gezogen wird. (Ein Teil, den Lean selbst
finden soll, schreibt man `_`.)
:::
:::solution
```
simp_rw [bind_comm (coin p) (coin q)]
```
:::
::::

::::circuit (height := "660") (size := "big") (route := "count") (inputs := "x y z w") (gates := "toNat, plus") (coins := "p ?|? p ?|?") (target := "nat 0:(1-p^2)^2 1:2p^2(1-p^2) 2:p^4") (start := "x>y.0; z>w.0") (context := "Lean/Rules.lean") (proof := "(p q : I) (n : ℕ) : (do let X ← binom p n; binom q X) = binom (p * q) n") (lemma := "binom_thin") (play := "y.T=p; y.F=0; w.T=p; w.F=0; a=toNat; b=toNat; c=plus; y>a.0; w>b.0; a>c.0; b>c.1; c>out") (uses := "binom_zero, pure_bind, binom_succ, bind_assoc, binom_add, bind_comm, coin_bind_binom', bind_pure, induction', rw, simp_rw")
:::en
*Boss: thinning a binomial.* Of $`n` throws with $`p`, each `true` is kept with probability $`q`. The number kept is binomial again: with which parameter?

On the board with $`n = 2` and `q = p`: two throws, each thinned, and the kept ones counted. The target is binomial with $`p^2`.
:::

:::de
*Endgegner: eine Binomialverteilung ausdünnen.* Von $`n` Würfen mit $`p` wird jedes `true` mit Wahrscheinlichkeit $`q` behalten. Die Anzahl der behaltenen ist wieder binomial: mit welchem Parameter?

Auf dem Spielfeld mit $`n = 2` und `q = p`: zwei Würfe, jeder ausgedünnt, und die behaltenen gezählt. Das Ziel ist binomial mit $`p^2`.
:::
:::solution
```
induction' n with n ih
rw [binom_zero, binom_zero, pure_bind, binom_zero]
rw [binom_succ, binom_succ (p * q), ← ih]
simp_rw [bind_assoc, pure_bind]
simp_rw [← binom_add]
simp_rw [bind_comm (binom p n) (binom q _)]
rw [coin_bind_binom']
```
:::
::::
