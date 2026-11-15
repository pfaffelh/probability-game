import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Coins that Wait" =>

%%%
htmlSplit := .never
%%%

:::en
Every board is given, and your task is always the same: choose what goes into the fields of the `bind`
gate, and drag it in. First, without coins, as in *Circuits*: the `bind` gate looks at `x` (on top)
and chooses a field, `T` or `F`, and the map in that field is applied to `y` (on the right side).

Then a coin waits: it is thrown *after* the coin `x`, and **which** coin it is depends on what `x`
showed. The waiting coin `y` is a `bind` box with a coin in each field: `coin p`, `coin (σ p)`,
`pure true` or `pure false`, each with its small histogram. `y` becomes
`bif x then coin q else coin r`: first throw `x`, then, depending on what came, the one or the other
coin. In Lean: `do let x ← coin p; let y ← (bif x then coin q else coin r); …`, that is
`coin p >>= fun x => …`.

This world is one of two ways after *Building with Coins*; the other is *Counting*. They do not need
each other.
:::

:::de
Jedes Spielfeld ist gegeben, und deine Aufgabe ist immer dieselbe: Wähle, was in die Felder des
Bausteins `bind` kommt, und zieh es hinein. Zuerst ohne Münzen, wie in *Schaltungen*: `bind` schaut auf
`x` (oben) und wählt ein Feld, `T` oder `F`, und die Abbildung in diesem Feld wird auf `y` (rechts)
angewandt.

Dann wartet eine Münze: Sie wird *nach* der Münze `x` geworfen, und **welche** Münze es ist, hängt davon
ab, was `x` zeigte. Die wartende Münze `y` ist ein `bind`-Kasten mit einer Münze in jedem Feld:
`coin p`, `coin (σ p)`, `pure true` oder `pure false`, jede mit ihrem kleinen Histogramm. `y` wird zu
`bif x then coin q else coin r`: erst `x` werfen, dann, je nachdem was kam, die eine oder die andere
Münze. In Lean: `do let x ← coin p; let y ← (bif x then coin q else coin r); …`, also

Diese Welt ist einer von zwei Wegen nach *Bauen mit Münzen*; der andere ist *Zählen*. Sie brauchen
einander nicht.
`coin p >>= fun x => …`.
:::

:::proofen
The statements are about the mass at `true`: the board shows the whole distribution, and your lemma
`bool_ext` says that the mass at `true` decides it. The new rule
`bind_true : (μ >>= f) true = μ true * f true true + μ false * f false true` goes both ways: through
`true` (the mass `μ true`, then the mass of `f true` at `true`) and through `false`.
:::

:::proofde
Die Aussagen handeln von der Masse bei `true`: Das Spielfeld zeigt die ganze Verteilung, und dein Lemma
`bool_ext` sagt, dass die Masse bei `true` sie festlegt. Die neue Regel
`bind_true : (μ >>= f) true = μ true * f true true + μ false * f false true` geht beide Wege: über
`true` (die Masse `μ true`, dann die Masse von `f true` bei `true`) und über `false`.
:::

::::circuit (height := "540") (inputs := "x y") (gates := "") (table := "0001") (goal := "x && y") (proof := "(x y : Bool) : (if x then y else false) = (bif x then (bif y then true else false) else (bif y then false else false))") (start := "a=bind@240,250; x>a.0; y>a.1; a>out") (play := "a.T=id; a.F=false") (uses := "-")
:::en
*A gate of your own.* First without coins, as in *Circuits*. There are four maps `Bool → Bool`:
`id`, `not`, always `T`, always `F` (see *Maps*). New gate: `bind`. It is on the board already, wired;
it has two fields, `T` and `F`, and your task is to put a map into each (drag it in, or tap the field
until it is the one you want). Read it from top to bottom: the input on top chooses
one of the two fields, `T` or `F` (the blue arrows). The value at the input on the right side goes
into both fields (the two circles, joined below them); the field chosen applies its map to it. In Lean:
`c >>= fun b => if b then f v else g v`. Make it `and`: when `x` is `true`, `y` itself; when `x` is
`false`, always `F`. (Tap a column of the output box: the field not used fades.)
:::

:::de
*Ein eigener Baustein.* Zuerst ohne Münzen, wie in *Schaltungen*. Es gibt vier Abbildungen
`Bool → Bool`: `id`, `not`, immer `T`, immer `F` (siehe *Abbildungen*). Neuer Baustein: `bind`. Er liegt
schon verdrahtet auf dem Spielfeld; er hat zwei Felder, `T` und `F`, und deine Aufgabe ist, in jedes
eine Abbildung zu legen (hineinziehen, oder das Feld antippen, bis es die richtige ist). Lies ihn von oben nach unten: Der
Eingang oben wählt eines der beiden Felder, `T` oder `F` (die blauen Pfeile). Der Wert am Eingang
rechts geht in beide Felder (die zwei Kreise, unten verbunden); das gewählte Feld wendet seine
Abbildung darauf an. In Lean:
`c >>= fun b => if b then f v else g v`. Mach daraus `and`: ist `x` `true`, `y` selbst; ist `x` `false`, immer
`F`. (Tippe eine Spalte des Ausgabekastens an: Das Feld, das nicht benutzt wird, verblasst.)
:::

:::proofen
Four rows, as in the boss of *Circuits*: by hand `cases x <;> cases y <;> rfl`, or
`decide +revert` (from *Maps*), which checks them all.

*Tip.* `decide +revert`.
:::

:::proofde
Vier Zeilen, wie beim Endgegner von *Schaltungen*: von Hand `cases x <;> cases y <;> rfl`, oder
`decide +revert` (aus *Abbildungen*), das alle prüft.

*Tipp.* `decide +revert`.
:::
:::solution
```
decide +revert
```
:::
::::

::::circuit (height := "540") (inputs := "x y") (gates := "") (table := "0110") (goal := "x ^^ y") (proof := "(x y : Bool) : (if x then !y else y) = (bif x then (bif y then false else true) else (bif y then true else false))") (start := "a=bind@240,250; x>a.0; y>a.1; a>out") (play := "a.T=not; a.F=id") (uses := "-")
:::en
*xor, chosen yourself.* `true` when exactly one input is. With `bind`: for `x = true` one map of `y`,
for `x = false` another. Four maps for each field: sixteen gates with two inputs, all of them.
:::

:::de
*xor, selbst gewählt.* `true`, wenn genau ein Eingang es ist. Mit `bind`: für `x = true` eine
Abbildung von `y`, für `x = false` eine andere. Vier Abbildungen für jedes Feld: sechzehn Bausteine mit
zwei Eingängen, alle.
:::

:::proofen
*Tip.* `decide +revert`.
:::

:::proofde
*Tipp.* `decide +revert`.
:::
:::solution
```
decide +revert
```
:::
::::

::::circuit (height := "540") (inputs := "x y") (gates := "") (table := "1101") (goal := "!x || y") (proof := "(x y : Bool) : (if x then y else true) = (bif x then (bif y then true else false) else (bif y then true else true))") (start := "a=bind@240,250; x>a.0; y>a.1; a>out") (play := "a.T=id; a.F=true") (uses := "-")
:::en
*If x, then y.* The implication: `false` only when `x` is `true` and `y` is `false`. In Lean
`!x || y`.
:::

:::de
*Wenn x, dann y.* Die Implikation: `false` nur, wenn `x` `true` ist und `y` `false`. In Lean
`!x || y`.
:::

:::proofen
*Tip.* `decide +revert`.
:::

:::proofde
*Tipp.* `decide +revert`.
:::
:::solution
```
decide +revert
```
:::
::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) : (μ >>= fun _ => μ) true = μ true * μ true + μ false * μ true") (new := "bind_true") (uses := "bind_true")
:::en
*Two ways to true.* The mass of a draw at `true`: through `true` and through `false`.
:::

:::de
*Zwei Wege zu true.* Die Masse eines Ziehens bei `true`: über `true` und über `false`.
:::

:::proofen
`bind_true : (μ >>= f) true = μ true * f true true + μ false * f false true`: the mass at the first step times the mass at `true` of what follows, for both values of the first step. That is the mass of a draw, by the definition of `>>=`:

```
(μ >>= f) b = ∑' a, μ a * (f a) b
```

on `Bool` a sum of two summands.

*Tip.* `rw [bind_true]`.
:::

:::proofde
`bind_true : (μ >>= f) true = μ true * f true true + μ false * f false true`: die Masse im ersten Schritt mal die Masse bei `true` dessen, was folgt, für beide Werte des ersten Schritts. Das ist die Masse eines Ziehens, nach der Definition von `>>=`:

```
(μ >>= f) b = ∑' a, μ a * (f a) b
```

auf `Bool` eine Summe aus zwei Summanden.

*Tipp.* `rw [bind_true]`.
:::
:::solution
```
rw [bind_true]
```
:::
::::

::::circuit (height := "480") (inputs := "x y") (gates := "") (coins := "p ?|?") (target := "bool true:p^2 false:1-p^2") (start := "x>y.0; y>out") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← (bif x then coin p else pure false); pure y) true = (↑p * ↑p : ENNReal)") (play := "y.T=p; y.F=0") (uses := "bind_true")
:::en
*Only after true.* `y` is a coin when `x` showed `true`, and surely `false` otherwise: choose its two
coins. Compare with *Both `true`* of *Building with Coins*: the same distribution,
without an `and`.
:::

:::de
*Nur nach true.* `y` ist eine Münze, wenn `x` `true` zeigte, und sonst sicher `false`: Wähle seine zwei
Münzen. Vergleiche mit *Beide `true`* aus *Bauen mit Münzen*: dieselbe Verteilung,
ohne ein `and`.
:::

:::proofen
`let y ← m; pure y` is just `m` (Lean drops it already when it reads the statement). `rw [bind_true]`
splits the mass at `true` into the two ways. What is left is computing: which coin each way takes, its
mass at `true`, products and sums. `norm_num` (from *Building with Coins*) does all that.

*Tip.* `rw [bind_true]`, then `norm_num`.
:::

:::proofde
`let y ← m; pure y` ist einfach `m` (Lean lässt es schon beim Lesen der Aussage weg). `rw [bind_true]`
teilt die Masse bei `true` in die zwei Wege. Was bleibt, ist Rechnen: welche Münze jeder Weg nimmt, ihre
Masse bei `true`, Produkte und Summen. `norm_num` (aus *Bauen mit Münzen*) erledigt das.

*Tipp.* `rw [bind_true]`, dann `norm_num`.
:::
:::solution
```
rw [bind_true]
norm_num
```
:::
::::

::::circuit (height := "480") (inputs := "x y") (gates := "") (coins := "p ?|?") (target := "bernoulli p") (start := "x>y.0; y>out") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← (bif x then pure true else pure false); pure y) true = (↑p : ENNReal)") (play := "y.T=1; y.F=0") (uses := "bind_true")
:::en
*Copying.* `y` is surely `true` after `true`, and surely `false` after `false`: it copies `x`. The
output `y` has the distribution of the coin `x`.
:::

:::de
*Abschreiben.* `y` ist sicher `true` nach `true` und sicher `false` nach `false`: Es schreibt `x` ab.
Der Ausgang `y` hat die Verteilung der Münze `x`.
:::

:::proofen
As before; now both ways end in a point mass, `pure true` and `pure false`.

*Tip.* `rw [bind_true]`, `norm_num`.
:::

:::proofde
Wie eben; jetzt enden beide Wege in einer Punktmasse, `pure true` und `pure false`.

*Tipp.* `rw [bind_true]`, `norm_num`.
:::
:::solution
```
rw [bind_true]
norm_num
```
:::
::::

::::circuit (height := "480") (inputs := "x y") (gates := "") (coins := "p ?|?") (target := "bool true:2p-p^2 false:(1-p)^2") (start := "x>y.0; y>out") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← (bif x then pure true else coin p); pure y) true = (↑p + ↑(σ p) * ↑p : ENNReal)") (play := "y.T=1; y.F=p") (uses := "bind_true")
:::en
*One more try.* When `x` showed `true`, that is enough: `y` is surely `true`. When it showed `false`,
throw again. Compare with *At least one `true`* of *Building with Coins*: the same as `x || y`, but the
second coin is only thrown when it is needed.
:::

:::de
*Noch ein Versuch.* Zeigte `x` `true`, reicht das: `y` ist sicher `true`. Zeigte es `false`, wirf noch
einmal. Vergleiche mit *Mindestens einmal `true`* aus *Bauen mit Münzen*: dasselbe wie `x || y`, aber die
zweite Münze wird nur geworfen, wenn sie gebraucht wird.
:::

:::proofen
The way through `true` has mass $`p \cdot 1`, the way through `false` mass $`(1 - p) \cdot p`.

*Tip.* `rw [bind_true]`, `norm_num`.
:::

:::proofde
Der Weg über `true` hat die Masse $`p \cdot 1`, der Weg über `false` die Masse $`(1 - p) \cdot p`.

*Tipp.* `rw [bind_true]`, `norm_num`.
:::
:::solution
```
rw [bind_true]
norm_num
```
:::
::::

::::circuit (height := "480") (inputs := "x y") (gates := "") (coins := "p ?|?") (target := "bool true:1-2p+2p^2 false:2p-2p^2") (start := "x>y.0; y>out") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← (bif x then coin p else coin (σ p)); pure y) true = (↑p * ↑p + ↑(σ p) * ↑(σ p) : ENNReal)") (play := "y.T=p; y.F=1-p") (uses := "bind_true")
:::en
*A coin that remembers.* After `true` the coin `p` again, after `false` the flipped coin $`1 - p`:
the second throw tends to repeat the first.
:::

:::de
*Eine Münze, die sich erinnert.* Nach `true` wieder die Münze `p`, nach `false` die umgedrehte Münze
$`1 - p`: Der zweite Wurf wiederholt eher den ersten.
:::

:::proofen
Two different coins in the two ways now, `coin p` and `coin (σ p)`; `norm_num` knows the masses of
both.

*Tip.* `rw [bind_true]`, `norm_num`.
:::

:::proofde
Jetzt zwei verschiedene Münzen in den zwei Wegen, `coin p` und `coin (σ p)`; `norm_num` kennt die
Massen beider.

*Tipp.* `rw [bind_true]`, `norm_num`.
:::
:::solution
```
rw [bind_true]
norm_num
```
:::
::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) : (do let x ← μ; let y ← pure (!x); pure (!y)) = μ") (new := "pure_bind, bind_pure") (uses := "pure_bind, Bool.not_not, bind_pure")
:::en
*Flip, and flip back.* A *Markov chain* goes step by step; each step depends only on where it is. The simplest one on `Bool`: every step flips. After two steps it is back where it started: whatever the start `μ`, the distribution is `μ` again.
:::

:::de
*Umdrehen, und zurück.* Eine *Markov-Kette* geht Schritt für Schritt; jeder Schritt hängt nur davon ab, wo sie gerade ist. Die einfachste auf `Bool`: Jeder Schritt dreht um. Nach zwei Schritten ist sie wieder am Anfang: Was auch immer der Start `μ` ist, die Verteilung ist wieder `μ`.
:::

:::proofen
Each step is sure: `pure_bind : (do let x ← pure a; f x) = f a`. Then your lemma from *Circuits*, `Bool.not_not : (!(!b)) = b`, and `bind_pure : (do let x ← μ; pure x) = μ`. All under the `do`: `simp only`.

*Tip.* `simp only [pure_bind, Bool.not_not, bind_pure]`.
:::

:::proofde
Jeder Schritt ist sicher: `pure_bind : (do let x ← pure a; f x) = f a`. Dann dein Lemma aus *Schaltungen*, `Bool.not_not : (!(!b)) = b`, und `bind_pure : (do let x ← μ; pure x) = μ`. Alles unter dem `do`: `simp only`.

*Tipp.* `simp only [pure_bind, Bool.not_not, bind_pure]`.
:::
:::solution
```
simp only [pure_bind, Bool.not_not, bind_pure]
```
:::
::::

::::leanonly (proof := "(p q r : I) : (do let x ← coin p; bif x then coin q else coin r) true = (↑p * ↑q + ↑(σ p) * ↑r : ENNReal)") (uses := "bind_true, Bool.cond_true, Bool.cond_false, coin_true, coin_false")
:::en
*One step forward.* A chain starts with `coin p`. From `true` the next step is `coin q`, from `false` it is `coin r`. The start distribution is carried one step forward: at `true` arrives $`p q + (1 - p) r`.
:::

:::de
*Ein Schritt nach vorn.* Eine Kette startet mit `coin p`. Von `true` aus ist der nächste Schritt `coin q`, von `false` aus `coin r`. Die Startverteilung wird einen Schritt nach vorn getragen: Bei `true` kommt $`p q + (1 - p) r` an.
:::

:::proofen
`bind_true`, the two branches, and the masses of the coins.

*Tip.* `rw [bind_true, Bool.cond_true, Bool.cond_false]`, `rw [coin_true, coin_true, coin_true, coin_false]`.
:::

:::proofde
`bind_true`, die zwei Zweige, und die Massen der Münzen.

*Tipp.* `rw [bind_true, Bool.cond_true, Bool.cond_false]`, `rw [coin_true, coin_true, coin_true, coin_false]`.
:::
:::solution
```
rw [bind_true, Bool.cond_true, Bool.cond_false]
rw [coin_true, coin_true, coin_true, coin_false]
```
:::
::::

::::leanonly (proof := "(p q r : I) : (do let x ← coin p; bif x then coin q else coin r) false = (↑p * ↑(σ q) + ↑(σ p) * ↑(σ r) : ENNReal)") (new := "bind_false") (uses := "bind_false, Bool.cond_true, Bool.cond_false, coin_true, coin_false")
:::en
*...and at false.* The rest of the distribution after the step: at `false` arrives $`p (1 - q) + (1 - p)(1 - r)`. Now the whole distribution after one step is known.
:::

:::de
*...und bei false.* Der Rest der Verteilung nach dem Schritt: Bei `false` kommt $`p (1 - q) + (1 - p)(1 - r)` an. Jetzt ist die ganze Verteilung nach einem Schritt bekannt.
:::

:::proofen
`bind_false : (μ >>= f) false = μ true * f true false + μ false * f false false`.

*Tip.* `rw [bind_false, Bool.cond_true, Bool.cond_false]`, `rw [coin_true, coin_false, coin_false, coin_false]`.
:::

:::proofde
`bind_false : (μ >>= f) false = μ true * f true false + μ false * f false false`.

*Tipp.* `rw [bind_false, Bool.cond_true, Bool.cond_false]`, `rw [coin_true, coin_false, coin_false, coin_false]`.
:::
:::solution
```
rw [bind_false, Bool.cond_true, Bool.cond_false]
rw [coin_true, coin_false, coin_false, coin_false]
```
:::
::::

::::leanonly (proof := "(p q r : I) (h : ↑p * ↑q + ↑(σ p) * ↑r = (↑p : ENNReal)) : (do let x ← coin p; bif x then coin q else coin r) = coin p") (uses := "bool_ext, bind_true, Bool.cond_true, Bool.cond_false, coin_true, coin_false")
:::en
*A distribution that stays.* When does the step carry `coin p` to itself? When the mass at `true` after the step is $`p` again: $`p = p q + (1 - p) r`. Then `coin p` is *stationary*: the chain started there stays there, step after step.
:::

:::de
*Eine Verteilung, die bleibt.* Wann trägt der Schritt `coin p` zu sich selbst? Wenn die Masse bei `true` nach dem Schritt wieder $`p` ist: $`p = p q + (1 - p) r`. Dann ist `coin p` *stationär*: Die dort gestartete Kette bleibt dort, Schritt für Schritt.
:::

:::proofen
Two distributions on `Bool` with the same mass at `true` are the same: `apply bool_ext`. Then the computation of *One step forward*, and the hypothesis `h`.

*Tip.* `apply bool_ext`, `rw [bind_true, Bool.cond_true, Bool.cond_false]`, `rw [coin_true, coin_true, coin_true, coin_false]`, `exact h`.
:::

:::proofde
Zwei Verteilungen auf `Bool` mit derselben Masse bei `true` sind gleich: `apply bool_ext`. Dann die Rechnung aus *Ein Schritt nach vorn*, und die Annahme `h`.

*Tipp.* `apply bool_ext`, `rw [bind_true, Bool.cond_true, Bool.cond_false]`, `rw [coin_true, coin_true, coin_true, coin_false]`, `exact h`.
:::
:::solution
```
apply bool_ext
rw [bind_true, Bool.cond_true, Bool.cond_false]
rw [coin_true, coin_true, coin_true, coin_false]
exact h
```
:::
::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) [Prob μ] (q : I) : (do let x ← μ; bif x then coin q else coin q) = coin q") (new := "cond_same, prob_unused") (uses := "cond_same, prob_unused")
:::en
*A chain that forgets.* If the next step does not depend on where the chain is (`q = r`), one step is enough to forget the start: whatever `μ` was, after the step it is `coin q`.
:::

:::de
*Eine Kette, die vergisst.* Hängt der nächste Schritt nicht davon ab, wo die Kette ist (`q = r`), genügt ein Schritt, um den Start zu vergessen: Was auch immer `μ` war, nach dem Schritt ist es `coin q`.
:::

:::proofen
`cond_same : (bif c then a else a) = a` (under the `do`: `simp only`), and `prob_unused : (do let _ ← μ; ν) = ν` for a distribution `μ` (`[Prob μ]`).

*Tip.* `simp only [cond_same]`, `rw [prob_unused]`.
:::

:::proofde
`cond_same : (bif c then a else a) = a` (unter dem `do`: `simp only`), und `prob_unused : (do let _ ← μ; ν) = ν` für eine Verteilung `μ` (`[Prob μ]`).

*Tipp.* `simp only [cond_same]`, `rw [prob_unused]`.
:::
:::solution
```
simp only [cond_same]
rw [prob_unused]
```
:::
::::

::::circuit (inputs := "x y z") (gates := "") (coins := "p ?|? ?|?") (target := "bool true:3p-3p^2+p^3 false:(1-p)^3") (start := "x>y.0; y>z.0; z>out") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← (bif x then pure true else coin p); let z ← (bif y then pure true else coin p); pure z) true = (↑p + ↑(σ p) * (↑p + ↑(σ p) * ↑p) : ENNReal)") (play := "y.T=1; y.F=p; z.T=1; z.F=p") (uses := "bind_true")
:::en
*Boss: three tries.* Throw until `true` comes, at most three times. `y` waits for `x`, and `z` waits
for `y`. `false` only when all three tries fail: $`(1 - p)^3`.
:::

:::de
*Boss: drei Versuche.* Wirf, bis `true` kommt, höchstens dreimal. `y` wartet auf `x`, und `z` wartet auf
`y`. `false` nur, wenn alle drei Versuche scheitern: $`(1 - p)^3`.
:::

:::proofen
`bind_true` twice. After the first, the way through `false` is a bind again, inside the computation,
where `rw` would have to pick the right place: give the rule to `norm_num` instead,
`norm_num [bind_true]`, and it uses it wherever it fits. (The way through `true` starts with
`pure true`; `pure_bind` throws it away, and `norm_num` knows that rule by itself.)

*Tip.* `rw [bind_true]`, then `norm_num [bind_true]`.
:::

:::proofde
Zweimal `bind_true`. Nach dem ersten ist der Weg über `false` wieder ein bind, mitten in der Rechnung,
wo `rw` die richtige Stelle treffen müsste: Gib die Regel stattdessen `norm_num`,
`norm_num [bind_true]`, und es benutzt sie, wo sie passt. (Der Weg über `true` beginnt mit
`pure true`; `pure_bind` wirft es weg, und diese Regel kennt `norm_num` von selbst.)

*Tipp.* `rw [bind_true]`, dann `norm_num [bind_true]`.
:::
:::solution
```
rw [bind_true]
norm_num [bind_true]
```
:::
::::
