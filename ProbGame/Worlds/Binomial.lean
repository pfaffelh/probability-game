import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Counting" =>

%%%
htmlSplit := .never
%%%

:::en
Throw $`n` coins and count how often `true` comes up: that is the *binomial distribution*
$`B(n, p)`, with $`P(k) = \binom{n}{k} p^k (1 - p)^{n - k}`. In *Building with Coins* you built
$`B(2, p)` from two coins; from the third level on it is a building block of its own.
:::

:::proofen
In Lean it is `binom p n`.
:::

:::de
Wirf $`n` Münzen und zähle, wie oft `true` kommt: Das ist die *Binomialverteilung* $`B(n, p)`, mit
$`P(k) = \binom{n}{k} p^k (1 - p)^{n - k}`. In *Bauen mit Münzen* hast du $`B(2, p)` aus zwei
Münzen gebaut; ab dem dritten Level ist sie ein eigener Baustein.
:::

:::proofde
In Lean heißt sie `binom p n`.
:::

::::build (target := "nat 0:(1-p)^3 1:3p(1-p)^2 2:3p^2(1-p) 3:p^3") (moves := "toNat, add") (coins := "3") (no := "4.1") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; let z ← coin p; pure (x.toNat + y.toNat + z.toNat)) = binom p 3")
:::en
*Three coins.* Count the `true`s among three coins.
:::

:::de
*Drei Münzen.* Zähle die `true` unter drei Münzen.
:::

:::proofen
Three throws are `binom p 3`. New: `add_assoc : a + b + c = a + (b + c)`.

*Tip.* As in *Building with Coins*, level 7, and `add_assoc` in the `simp only`.
:::

:::proofde
Drei Würfe sind `binom p 3`. Neu: `add_assoc : a + b + c = a + (b + c)`.

*Tipp.* Wie in *Bauen mit Münzen*, Level 7, und `add_assoc` im `simp only`.
:::
::::

::::build (target := "nat 0:1-p 1:p") (moves := "not, toNat") (coins := "1") (no := "4.2") (proof := "(p : I) : Bool.toNat <$> coin p = binom p 1") (lemma := "binom_one")
:::en
*$`B(1, p)`.* One throw, counted: a coin as a number.
:::

:::de
*$`B(1, p)`.* Ein Wurf, gezählt: eine Münze als Zahl.
:::

:::proofen
One coin as a number is $`B(1, p)`. The lemma you prove here is called `binom_one`; from the
next level on it is in your inventory. And `map_eq_pure_bind` from *Draw, then Compute*.

*Tip.* `rw [binom_succ, binom_zero]`, `simp only [pure_bind, add_zero]`, `rw [map_eq_pure_bind]`.
:::

:::proofde
Eine Münze als Zahl ist $`B(1, p)`. Das Lemma, das du hier beweist, heißt `binom_one`; ab dem
nächsten Level ist es in deinem Inventar. Und `map_eq_pure_bind` aus *Erst ziehen, dann rechnen*.

*Tipp.* `rw [binom_succ, binom_zero]`, `simp only [pure_bind, add_zero]`, `rw [map_eq_pure_bind]`.
:::
::::

::::build (target := "nat 0:(1-p)^3 1:3p(1-p)^2 2:3p^2(1-p) 3:p^3") (moves := "toNat, add") (sources := "coin:1, binom2:1") (no := "4.3") (proof := "(p : I) (n : ℕ) : (do let X ← binom p n; let Y ← coin p; pure (X + Y.toNat)) = binom p (n + 1)") (lemma := "binom_succ'")
:::en
*A new building block.* $`B(2, p)` and one more coin give $`B(3, p)`: one more throw, one more
chance to count.
:::

:::de
*Ein neuer Baustein.* $`B(2, p)` und eine weitere Münze ergeben $`B(3, p)`: ein Wurf mehr, eine
Chance mehr zu zählen.
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
::::

::::build (target := "bool true:2p-p^2 false:(1-p)^2") (moves := "toNat, add, pos") (sources := "binom2:1") (no := "4.4") (proof := "(p : I) : (fun n => decide (1 ≤ n)) <$> binom p 2 = (do let x ← coin p; let y ← coin p; pure (x || y))")
:::en
*At least one `true`*, as in *Building with Coins*, but this time from $`B(2, p)`: when is a number at least $`1`?
:::

:::de
*Mindestens einmal `true`*, wie in *Bauen mit Münzen*, aber diesmal aus $`B(2, p)`: Wann ist eine Zahl mindestens
$`1`?
:::

:::proofen
At least $`1` out of $`B(2, p)` is: at least one of two coins.

*Tip.* As in the boss of *Building with Coins*: unfold, clean up, go under the throws, four cases.
:::

:::proofde
Mindestens $`1` aus $`B(2, p)` heißt: mindestens eine von zwei Münzen.

*Tipp.* Wie beim Endgegner von *Bauen mit Münzen*: auswickeln, aufräumen, unter die Würfe gehen, vier Fälle.
:::
::::

::::build (target := "nat 0:(1-p)^4 1:4p(1-p)^3 2:6p^2(1-p)^2 3:4p^3(1-p) 4:p^4") (moves := "add, max") (sources := "binom2:2") (no := "4.5") (proof := "(p : I) (n m : ℕ) : (do let X ← binom p n; let Y ← binom p m; pure (X + Y)) = binom p (n + m)") (lemma := "binom_add")
:::en
*Boss: $`B(2, p) * B(2, p) = B(4, p)`.* Two independent binomials, no coins. The sum of independent
random numbers has the *convolution* $`*` of their distributions as its distribution.
:::

:::de
*Endgegner: $`B(2, p) * B(2, p) = B(4, p)`.* Zwei unabhängige Binomialverteilungen, keine Münzen. Die
Summe unabhängiger Zufallszahlen hat die *Faltung* $`*` ihrer Verteilungen als Verteilung.
:::

:::proofen
*Boss.* On the board it was $`B(2, p) * B(2, p) = B(4, p)`; here it is for all $`n` and $`m`: the
sum of independent binomials is binomial. Here `bind_pure` from *Draw, then Compute* is needed again.

*Tip.* Induction on `m`. Case $`0`: `rw [binom_zero]`, `simp only [pure_bind, add_zero, bind_pure]`.
Case $`m + 1`: write `binom p (m + 1)` with `← binom_succ' p m`, then `n + (m + 1)` as
`n + m + 1` (`← add_assoc`) and that again with `← binom_succ' p (n + m)`; now `← ih`, and clean up
with `simp only [bind_assoc, pure_bind, add_assoc]`.
:::

:::proofde
*Endgegner.* Auf dem Spielfeld war es $`B(2, p) * B(2, p) = B(4, p)`; hier gilt es für alle $`n`
und $`m`: Die Summe unabhängiger Binomialverteilungen ist binomial. Hier wird wieder `bind_pure` aus
*Erst ziehen, dann rechnen* gebraucht.

*Tipp.* Induktion nach `m`. Fall $`0`: `rw [binom_zero]`, `simp only [pure_bind, add_zero, bind_pure]`.
Fall $`m + 1`: schreibe `binom p (m + 1)` mit `← binom_succ' p m` um, dann `n + (m + 1)` als
`n + m + 1` (`← add_assoc`) und das wieder mit `← binom_succ' p (n + m)`; jetzt `← ih`, und räume auf
mit `simp only [bind_assoc, pure_bind, add_assoc]`.
:::
::::
