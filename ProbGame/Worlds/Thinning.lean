import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Thinning" =>

%%%
htmlSplit := .never
%%%

:::en
A coin is *thinned* when each `true` is kept only with probability $`q`, decided by a second coin. In Lean only. This way is picked up again in *Binomial*.
:::

:::de
Eine Münze wird *ausgedünnt*, wenn jedes `true` nur mit Wahrscheinlichkeit $`q` behalten wird; eine zweite Münze entscheidet. Nur in Lean. Dieser Weg wird in *Binomial* wieder aufgegriffen.
:::

::::leanonly (proof := "(p q : I) : coin (p * q) true = (↑p * ↑q : ENNReal)") (new := "mass_mul") (uses := "coin_true, mass_mul, coin_false, coin_total")
:::en
*A product of chances.* `p * q` is again a number in $`[0, 1]`, and as a mass it is the product of the masses.
:::

:::de
*Ein Produkt von Chancen.* `p * q` ist wieder eine Zahl in $`[0, 1]`, und als Masse ist es das Produkt der Massen.
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

::::leanonly (proof := "(p q : I) : (do let x ← coin p; bif x then coin q else pure false) = coin (p * q)") (lemma := "coin_thin") (new := "mul_zero, add_zero") (uses := "bool_ext, bind_true, Bool.cond_true, Bool.cond_false, pure_true, mul_zero, add_zero, coin_true, mass_mul, bind_false, zero_add, coin_false, coin_total")
:::en
*Keeping with probability q.* A coin `p` is thrown; a `true` is kept with probability $`q` (a second coin `q` decides), a `false` stays `false`. What is left is a coin `p * q`: the coin is *thinned*.
:::

:::de
*Behalten mit Wahrscheinlichkeit q.* Eine Münze `p` wird geworfen; ein `true` wird mit Wahrscheinlichkeit $`q` behalten (eine zweite Münze `q` entscheidet), ein `false` bleibt `false`. Übrig bleibt eine Münze `p * q`: Die Münze wird *ausgedünnt*.
:::

:::proofen
Two distributions on `Bool` are the same when their masses at `true` are: `apply bool_ext`. Then `bind_true` from *Coins that Wait*, the two `bif`, and `pure_true`. New: `mul_zero : a * 0 = 0` and `add_zero : a + 0 = a`.

*Tip.* `apply bool_ext`, `rw [bind_true, Bool.cond_true, Bool.cond_false]`, `rw [pure_true, Bool.cond_false, mul_zero, add_zero]`, `rw [coin_true, coin_true, coin_true, mass_mul]`.
:::

:::proofde
Zwei Verteilungen auf `Bool` sind gleich, wenn ihre Massen bei `true` gleich sind: `apply bool_ext`. Dann `bind_true` aus *Münzen, die warten*, die zwei `bif` und `pure_true`. Neu: `mul_zero : a * 0 = 0` und `add_zero : a + 0 = a`.

*Tipp.* `apply bool_ext`, `rw [bind_true, Bool.cond_true, Bool.cond_false]`, `rw [pure_true, Bool.cond_false, mul_zero, add_zero]`, `rw [coin_true, coin_true, coin_true, mass_mul]`.
:::
:::solution
```
apply bool_ext
rw [bind_true, Bool.cond_true, Bool.cond_false]
rw [pure_true, Bool.cond_false, mul_zero, add_zero]
rw [coin_true, coin_true, coin_true, mass_mul]
```
:::
::::

::::leanonly (proof := "(p q : I) : (do let x ← coin p; bif x then coin q else pure false) = (do let x ← coin q; bif x then coin p else pure false)") (new := "mul_comm") (uses := "coin_thin, mul_comm")
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

::::leanonly (proof := "(p q r : I) : (do let x ← coin p; let y ← (bif x then coin q else pure false); bif y then coin r else pure false) = coin (p * q * r)") (new := "bind_assoc") (uses := "bind_assoc, coin_thin")
:::en
*Boss: thinning twice.* Thinned with $`q`, and the rest thinned again with $`r`.
:::

:::de
*Endgegner: zweimal ausdünnen.* Mit $`q` ausgedünnt, und der Rest noch einmal mit $`r`.
:::

:::proofen
The first two steps are one coin, once they are a `do` block of their own: `rw [← bind_assoc]` (`bind_assoc : (μ >>= f) >>= g = μ >>= fun x => f x >>= g`). Then your lemma, twice.

*Tip.* `rw [← bind_assoc, coin_thin, coin_thin]`.
:::

:::proofde
Die ersten zwei Schritte sind eine Münze, sobald sie ein eigener `do`-Block sind: `rw [← bind_assoc]` (`bind_assoc : (μ >>= f) >>= g = μ >>= fun x => f x >>= g`). Dann dein Lemma, zweimal.

*Tipp.* `rw [← bind_assoc, coin_thin, coin_thin]`.
:::
:::solution
```
rw [← bind_assoc, coin_thin, coin_thin]
```
:::
::::
