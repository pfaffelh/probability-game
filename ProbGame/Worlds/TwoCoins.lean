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

*Check* compares the selected line (or else the newest) with the target, for every $`p`.
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

*Prüfen* vergleicht die ausgewählte Leitung (sonst die neueste) mit dem Ziel, für jedes $`p`.
:::

:::proofde
Der Schaltplan, von links nach rechts gelesen, ist ein `do`-Block in Lean.
:::

::::build (target := "bool true:p^2 false:1-p^2") (moves := "not, and, or") (coins := "2") (no := "3.1") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure (x && y)) = coin (p * p)")
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
::::

::::build (target := "bool true:p(1-p) false:1-p(1-p)") (moves := "not, and, or") (coins := "2") (no := "3.2") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure (x && !y)) = coin (p * σ p)")
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
::::

::::build (target := "bool true:2p-p^2 false:(1-p)^2") (moves := "not, and, or") (coins := "2") (no := "3.3") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure (x || y)) = coin (σ (σ p * σ p))")
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
::::

::::build (target := "pure false") (moves := "not, and, or") (coins := "1") (no := "3.4") (proof := "(p : I) : (do let x ← coin p; pure (x && !x)) = pure false")
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
::::

::::build (target := "pure true") (moves := "not, and, or") (coins := "1") (no := "3.5") (proof := "(p : I) : (do let x ← coin p; pure (x || !x)) = pure true")
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
::::

::::build (target := "bool true:2p(1-p) false:p^2+(1-p)^2") (moves := "not, and, or") (coins := "2") (no := "3.6") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure ((x || y) && !(x && y))) = (do let x ← coin p; let y ← coin p; pure (xor x y))")
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
::::

::::build (target := "nat 0:(1-p)^2 1:2p(1-p) 2:p^2") (moves := "not, and, or, toNat, add") (coins := "2") (no := "3.7") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure (x.toNat + y.toNat)) = binom p 2")
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
::::

::::build (target := "bool true:3p^2-2p^3 false:1-3p^2+2p^3") (moves := "not, and, or") (coins := "3") (no := "3.8") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; let z ← coin p; pure ((x && y) || (x && z) || (y && z))) = (fun n => decide (2 ≤ n)) <$> binom p 3")
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
::::
