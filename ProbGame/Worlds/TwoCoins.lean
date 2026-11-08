import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Building with Coins" =>

%%%
htmlSplit := .never
%%%

:::en
Now you build a circuit. The coins of the level lie there from the start, each as a line; all coins
have the same $`p` and are independent of each other. Tap one or several lines (a tap beside them
chooses none again), then a function: a column takes the
lines with a dot as its inputs, and its result runs on as a new line. A line that a column only
crosses, without a dot, is not used. A coin may go into several functions; then the results depend
on each other, and the game takes that into account. At the end of each line is its distribution,
found by going through all outcomes of the coins it comes from: with two coins, `true`–`true` has
mass $`p^2`, `true`–`false` $`p(1 - p)`, and so on.

*Check* compares the chosen line with the target, for every $`p`; for this, exactly one line is chosen. *Delete*
removes the chosen lines and all that is built on them.
:::

:::proofen
The circuit, read from left to right, is a `do` block in Lean.
:::

:::de
Jetzt baust du einen Schaltplan. Die Münzen des Levels liegen von Anfang an da, jede als Leitung;
alle Münzen haben dasselbe $`p` und sind unabhängig voneinander. Tippe eine oder mehrere Leitungen an
(ein Tipp daneben hebt die Auswahl wieder auf), dann eine Funktion: Eine Spalte nimmt die Leitungen mit einem Punkt als Eingänge, und ihr Ergebnis läuft als
neue Leitung weiter. Eine Leitung, die eine Spalte nur kreuzt, ohne Punkt, wird nicht benutzt. Eine
Münze darf in mehrere Funktionen gehen; dann hängen die Ergebnisse voneinander ab, und das Spiel
berücksichtigt das. Am Ende jeder Leitung steht ihre Verteilung, die sich ergibt, indem man alle
Ausgänge der Münzen durchgeht, aus denen sie kommt: Bei zwei Münzen hat `true`–`true` die Masse
$`p^2`, `true`–`false` $`p(1 - p)`, und so weiter.

*Prüfen* vergleicht die ausgewählte Leitung mit dem Ziel, für jedes $`p`; dafür ist genau eine Leitung ausgewählt.
*Löschen* entfernt die ausgewählten Leitungen und alles, was auf ihnen gebaut ist.
:::

:::proofde
Der Schaltplan, von links nach rechts gelesen, ist ein `do`-Block in Lean.
:::

::::build (target := "bool true:p^2 false:1-p^2") (moves := "not, and, or") (coins := "2") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure (x && y)) = coin (p * p)") (new := "coin_and") (play := "M1 M2 and")
:::en
*Both `true`.* Two coins, and `true` only when both show `true`.
:::

:::de
*Beide `true`.* Zwei Münzen, und `true` nur, wenn beide `true` zeigen.
:::

:::proofen
Your circuit, read from left to right, is a `do` block, as in *Draw, then Compute*: `let x ← coin p`
throws a coin and calls its result `x`, and `pure` at the end is the result. Now there are two
throws, and each `←` is a new throw, independent of the others. The new rule is independence itself:
`coin_and : (do let x ← coin p; let y ← coin q; pure (x && y)) = coin (p * q)`.
:::

:::proofde
Dein Schaltplan, von links nach rechts gelesen, ist ein `do`-Block, wie in *Erst ziehen, dann
rechnen*: `let x ← coin p` wirft eine Münze und nennt ihr Ergebnis `x`, und `pure` am Ende ist das
Ergebnis. Jetzt gibt es zwei Würfe, und jedes `←` ist ein neuer Wurf, unabhängig von den anderen. Die
neue Regel ist die Unabhängigkeit selbst:
`coin_and : (do let x ← coin p; let y ← coin q; pure (x && y)) = coin (p * q)`.
:::
:::solution
```
rw [coin_and]
```
:::
::::

::::build (target := "bool true:p(1-p) false:1-p(1-p)") (moves := "not, and, or") (coins := "2") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure (x && !y)) = coin (p * σ p)") (play := "M2 not; M1 Z1 and")
:::en
*First `true`, then `false`.*
:::

:::de
*Erst `true`, dann `false`.*
:::

:::proofen
Work backwards, on the right side: `rw [← coin_and]` uses the rule from right to left, and
`rw [← coin_not]` turns `coin (σ p)` into `not <$> coin p`. Then a move sits inside the `do` block,
and `bind_map_left` moves it into the result, as in *Draw, then Compute*; inside a `do` block, with
`simp only`.

*Tip.* `rw [← coin_and]`, `rw [← coin_not]`, `simp only [bind_map_left]`.
:::

:::proofde
Arbeite rückwärts, auf der rechten Seite: `rw [← coin_and]` benutzt die Regel von rechts nach
links, und `rw [← coin_not]` macht aus `coin (σ p)` ein `not <$> coin p`. Dann steht ein Zug im
`do`-Block, und `bind_map_left` schiebt ihn ins Ergebnis, wie in *Erst ziehen, dann rechnen*;
innerhalb eines `do`-Blocks mit `simp only`.

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

::::build (target := "bool true:2p-p^2 false:(1-p)^2") (moves := "not, and, or") (coins := "2") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure (x || y)) = coin (σ (σ p * σ p))") (new := "map_bind, or_eq") (play := "M1 M2 or")
:::en
*At least one `true`.* `false` only when both show `false`: $`(1 - p)^2`.
:::

:::de
*Mindestens einmal `true`.* `false` nur, wenn beide `false` zeigen: $`(1 - p)^2`.
:::

:::proofen
At least one `true` is: not both `false`, with probability $`1 - (1 - p)^2`. Two new rules: De
Morgan, `or_eq : (x || y) = !(!x && !y)`, and `map_bind : f <$> (do let x ← μ; g x) = (do let x ← μ; f <$> g x)`:
a move after a `do` block goes into it.

*Tip.* On the right side, backwards: `rw [← coin_not]`, `rw [← coin_and]`, `rw [← coin_not]`; then
`simp only [bind_map_left, map_bind, map_pure, or_eq]`.
:::

:::proofde
Mindestens einmal `true` heißt: nicht beide `false`, mit Wahrscheinlichkeit $`1 - (1 - p)^2`. Zwei
neue Regeln: De Morgan, `or_eq : (x || y) = !(!x && !y)`, und
`map_bind : f <$> (do let x ← μ; g x) = (do let x ← μ; f <$> g x)`: Ein Zug nach einem `do`-Block
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

::::build (target := "pure false") (moves := "not, and, or") (coins := "1") (proof := "(p : I) : (do let x ← coin p; pure (x && !x)) = pure false") (new := "Bool.and_not_self, coin_unused") (play := "M1 not; M1 Z1 and")
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

::::build (target := "pure true") (moves := "not, and, or") (coins := "1") (proof := "(p : I) : (do let x ← coin p; pure (x || !x)) = pure true") (new := "Bool.or_not_self") (play := "M1 not; M1 Z1 or")
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

::::build (target := "bool true:2p(1-p) false:p^2+(1-p)^2") (moves := "not, and, or") (coins := "2") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure ((x || y) && !(x && y))) = (do let x ← coin p; let y ← coin p; pure (xor x y))") (new := "<;>") (play := "M1 M2 or; M1 M2 and; Z2 not; Z1 Z3 and")
:::en
*Exactly one `true`*, without a function for it: at least one, but not both.
:::

:::de
*Genau einmal `true`*, ohne eine Funktion dafür: mindestens einmal, aber nicht beide.
:::

:::proofen
Exactly one `true` is `xor`. Both sides throw the same coins; go under the throws, with `congr 1`
and `funext x` (and again for `y`), and look at all four cases. New: `t₁ <;> t₂` runs `t₂` on every
goal that `t₁` leaves.

*Tip.* `congr 1`, `funext x`, `congr 1`, `funext y`, `cases x <;> cases y <;> rfl`.
:::

:::proofde
Genau einmal `true` ist `xor`. Beide Seiten werfen dieselben Münzen; geh unter die Würfe, mit
`congr 1` und `funext x` (und nochmal für `y`), und sieh dir alle vier Fälle an. Neu: `t₁ <;> t₂`
führt `t₂` auf jedem Ziel aus, das `t₁` übrig lässt.

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

::::build (target := "nat 0:(1-p)^2 1:2p(1-p) 2:p^2") (moves := "not, and, or, toNat, add") (coins := "2") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure (x.toNat + y.toNat)) = binom p 2") (new := "binom_zero, binom_succ, add_zero") (play := "M1 toNat; M2 toNat; Z1 Z2 add")
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
more. To clean up `do` blocks, the rules of *Draw, then Compute*: `bind_assoc` (a `do` block in a
`do` block is one `do` block) and `pure_bind : (do let x ← pure a; f x) = f a`; new is
`add_zero : n + 0 = n`.

*Tip.* `rw [binom_succ, binom_succ, binom_zero]`, then `simp only [bind_assoc, pure_bind, add_zero]`.
:::

:::proofde
Die Binomialverteilung `binom p n` ist definiert wie die natürlichen Zahlen im Natural Number Game:
durch Null und Nachfolger. `binom_zero : binom p 0 = pure 0`: kein Wurf, kein `true`.
`binom_succ : binom p (n + 1) = do let X ← coin p; let Y ← binom p n; pure (X.toNat + Y)`: ein Wurf
mehr. Zum Aufräumen von `do`-Blöcken die Regeln aus *Erst ziehen, dann rechnen*: `bind_assoc` (ein
`do`-Block in einem `do`-Block ist ein `do`-Block) und `pure_bind : (do let x ← pure a; f x) = f a`;
neu ist `add_zero : n + 0 = n`.

*Tipp.* `rw [binom_succ, binom_succ, binom_zero]`, dann `simp only [bind_assoc, pure_bind, add_zero]`.
:::
:::solution
```
rw [binom_succ, binom_succ, binom_zero]
simp only [bind_assoc, pure_bind, add_zero]
```
:::
::::

::::build (target := "nat 0:(1-p)^3 1:3p(1-p)^2 2:3p^2(1-p) 3:p^3") (moves := "toNat, add") (coins := "3") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; let z ← coin p; pure (x.toNat + y.toNat + z.toNat)) = binom p 3") (new := "add_assoc") (play := "M1 toNat; M2 toNat; M3 toNat; Z1 Z2 Z3 add")
:::en
*Three coins.* Count the `true`s among three coins. Throw $`n` coins and count how often `true`
comes up: that is the *binomial distribution* $`B(n, p)`, with
$`P(k) = \binom{n}{k} p^k (1 - p)^{n - k}`. From the next level on, $`B(2, p)` is a building block
of its own.
:::

:::de
*Drei Münzen.* Zähle die `true` unter drei Münzen. Wirf $`n` Münzen und zähle, wie oft `true`
kommt: Das ist die *Binomialverteilung* $`B(n, p)`, mit $`P(k) = \binom{n}{k} p^k (1 - p)^{n - k}`.
Ab dem nächsten Level ist $`B(2, p)` ein eigener Baustein.
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

::::build (target := "nat 0:(1-p)^3 1:3p(1-p)^2 2:3p^2(1-p) 3:p^3") (moves := "toNat, add") (sources := "binom2:1, coin:1") (proof := "(p : I) (n : ℕ) : (do let X ← binom p n; let Y ← coin p; pure (X + Y.toNat)) = binom p (n + 1)") (lemma := "binom_succ'") (new := "induction'") (play := "M1 toNat; B1 Z1 add")
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

::::build (target := "nat 0:(1-p)^4 1:4p(1-p)^3 2:6p^2(1-p)^2 3:4p^3(1-p) 4:p^4") (moves := "add") (sources := "binom2:2") (proof := "(p : I) (n m : ℕ) : (do let X ← binom p n; let Y ← binom p m; pure (X + Y)) = binom p (n + m)") (lemma := "binom_add") (play := "B1 B2 add")
:::en
*$`B(2, p) * B(2, p) = B(4, p)`.* Two independent binomials, no coins. The sum of independent
random numbers has the *convolution* $`*` of their distributions as its distribution.
:::

:::de
*$`B(2, p) * B(2, p) = B(4, p)`.* Zwei unabhängige Binomialverteilungen, keine Münzen. Die
Summe unabhängiger Zufallszahlen hat die *Faltung* $`*` ihrer Verteilungen als Verteilung.
:::

:::proofen
*For all $`n` and $`m`.* On the board it was $`B(2, p) * B(2, p) = B(4, p)`; here it is for all $`n` and $`m`: the
sum of independent binomials is binomial. Here `bind_pure` from *Draw, then Compute* is needed again.

*Tip.* Induction on `m`. Case $`0`: `rw [binom_zero]`, `simp only [pure_bind, add_zero, bind_pure]`.
Case $`m + 1`: write `binom p (m + 1)` with `← binom_succ' p m`, then `n + (m + 1)` as
`n + m + 1` (`← add_assoc`) and that again with `← binom_succ' p (n + m)`; now `← ih`, and clean up
with `simp only [bind_assoc, pure_bind, add_assoc]`.
:::

:::proofde
*Für alle $`n` und $`m`.* Auf dem Spielfeld war es $`B(2, p) * B(2, p) = B(4, p)`; hier gilt es für alle $`n`
und $`m`: Die Summe unabhängiger Binomialverteilungen ist binomial. Hier wird wieder `bind_pure` aus
*Erst ziehen, dann rechnen* gebraucht.

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

::::build (target := "bool true:3p^2-2p^3 false:1-3p^2+2p^3") (moves := "not, and, or") (coins := "3") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; let z ← coin p; pure ((x && y) || (x && z) || (y && z))) = (fun n => decide (2 ≤ n)) <$> binom p 3") (play := "M1 M2 and; M1 M3 and; M2 M3 and; Z1 Z2 Z3 or")
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
