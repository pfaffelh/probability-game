import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Building with Coins" =>

%%%
htmlSplit := .never
%%%

:::en
The circuits of the world *Circuits*, now with a coin at each input: `x ← coin p`, `y ← coin p`, …,
all with the same $`p` and thrown independently of each other. Then the output is random too: its
distribution is the target. Each row of the truth table has a mass, the product of the masses of its
inputs ($`p` for `true`, $`1 - p` for `false`): with two coins, `true`–`true` has mass $`p^2`,
`true`–`false` $`p(1 - p)`, and so on. The mass of the output at a value is the sum over the rows
where the output has that value. The output box below shows the target and your output, as masses and
as a small histogram (the target dashed); beside the board the bars.

A coin may go into several gates; then the results depend on each other, and the game takes that into
account.
:::

:::proofen
The circuit, read from top to bottom, is a `do` block in Lean: each coin a line `let x ← coin p`,
which *draws* `x` from the distribution `coin p`, and at the end `pure (…)`, a sure result, with what
the gates compute. A single gate is such a block too: `f <$> μ` is `do let x ← μ; pure (f x)`. Without
the words of `do`, the same reads `μ >>= fun x => pure (f x)`: `>>=` (*bind*) passes what `μ` drew to
the function after it, and `fun x => …` is that function. The proofs learn the rules of `do` blocks,
the *monad laws*, one at a time, when a level needs them.
:::

:::de
Die Schaltungen der Welt *Schaltungen*, jetzt mit einer Münze an jedem Eingang: `x ← coin p`,
`y ← coin p`, …, alle mit demselben $`p` und unabhängig voneinander geworfen. Dann ist auch der Ausgang
zufällig: Seine Verteilung ist das Ziel. Jede Zeile der Wahrheitstafel hat eine Masse, das Produkt der
Massen ihrer Eingänge ($`p` für `true`, $`1 - p` für `false`): Bei zwei Münzen hat `true`–`true` die
Masse $`p^2`, `true`–`false` $`p(1 - p)`, und so weiter. Die Masse des Ausgangs bei einem Wert ist die
Summe über die Zeilen, in denen der Ausgang diesen Wert hat. Der Ausgabekasten unten zeigt Ziel und
Ausgang, als Massen und als kleines Histogramm (das Ziel gestrichelt); neben dem Spielfeld die Säulen.

Eine Münze darf in mehrere Bausteine gehen; dann hängen die Ergebnisse voneinander ab, und das Spiel
berücksichtigt das.
:::

:::proofde
Die Schaltung, von oben nach unten gelesen, ist ein `do`-Block in Lean: jede Münze eine Zeile
`let x ← coin p`, die `x` aus der Verteilung `coin p` *zieht*, und am Ende `pure (…)`, ein sicheres
Ergebnis, mit dem, was die Bausteine rechnen. Auch ein einzelner Baustein ist so ein Block: `f <$> μ`
ist `do let x ← μ; pure (f x)`. Ohne die Wörter von `do` liest sich dasselbe
`μ >>= fun x => pure (f x)`: `>>=` (*bind*) gibt, was `μ` gezogen hat, an die Funktion danach weiter,
und `fun x => …` ist diese Funktion. Die Beweise lernen die Regeln der `do`-Blöcke, die
*Monadengesetze*, eine nach der anderen, wenn ein Level sie braucht.
:::

::::circuit (height := "440") (inputs := "x y") (gates := "and, or, not") (coins := "p p") (target := "bool true:p^2 false:1-p^2") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure (x && y)) = coin (p * p)") (new := "coin_and, norm_num") (play := "a=and; x>a.0; y>a.1; a>out")
:::en
*Both `true`.* Two coins, and `true` only when both show `true`.
:::

:::de
*Beide `true`.* Zwei Münzen, und `true` nur, wenn beide `true` zeigen.
:::

:::proofen
Your circuit, read from top to bottom, is a `do` block: `let x ← coin p`
throws a coin and calls its result `x`, and `pure` at the end is the result. Now there are two
throws, and each `←` is a new throw, independent of the others. The new rule is independence itself:
`coin_and : (do let x ← coin p; let y ← coin q; pure (x && y)) = coin (p * q)`.

New from now on: `norm_num` does the computing for you. It computes with numbers and masses (`p * 1`,
`a + 0`, `bif true then a else b`, the masses `coin p true = p` and `(pure b) true`, and taking away
a finite mass), and with `norm_num [h]` also with a rule `h` of yours. What is left to you are the
rules of the game.
:::

:::proofde
Dein Schaltplan, von oben nach unten gelesen, ist ein `do`-Block: `let x ← coin p` wirft eine Münze und nennt ihr Ergebnis `x`, und `pure` am Ende ist das
Ergebnis. Jetzt gibt es zwei Würfe, und jedes `←` ist ein neuer Wurf, unabhängig von den anderen. Die
neue Regel ist die Unabhängigkeit selbst:
`coin_and : (do let x ← coin p; let y ← coin q; pure (x && y)) = coin (p * q)`.

Neu ab jetzt: `norm_num` rechnet für dich. Es rechnet mit Zahlen und Massen (`p * 1`, `a + 0`,
`bif true then a else b`, die Massen `coin p true = p` und `(pure b) true`, und das Wegnehmen einer
endlichen Masse), und mit `norm_num [h]` auch mit einer Regel `h` von dir. Was dir bleibt, sind die
Regeln des Spiels.
:::
:::solution
```
rw [coin_and]
```
:::
::::

::::leanonly (proof := "(p : I) (f : Bool → DiscreteMeasure Bool) : (not <$> coin p) >>= f = coin p >>= (fun x => f (!x))") (new := "bind_map_left")
:::en
*A move before a draw.* Drawing from a moved coin is drawing from the coin and moving the result.
:::

:::de
*Ein Zug vor dem Ziehen.* Aus einer bewegten Münze ziehen heißt, aus der Münze ziehen und das Ergebnis bewegen.
:::

:::proofen
`μ >>= f` is the `do` block `do let x ← μ; f x`. `bind_map_left : (f <$> μ) >>= g = μ >>= fun x => g (f x)`.

*Tip.* `rw [bind_map_left]`.
:::

:::proofde
`μ >>= f` ist der `do`-Block `do let x ← μ; f x`. `bind_map_left : (f <$> μ) >>= g = μ >>= fun x => g (f x)`.

*Tipp.* `rw [bind_map_left]`.
:::
:::solution
```
rw [bind_map_left]
```
:::
::::

::::circuit (height := "540") (inputs := "x y") (gates := "and, or, not") (coins := "p p") (target := "bool true:p(1-p) false:1-p(1-p)") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure (x && !y)) = coin (p * σ p)") (new := "simp only") (play := "a=not; b=and; y>a.0; x>b.0; a>b.1; b>out")
:::en
*First `true`, then `false`.*
:::

:::de
*Erst `true`, dann `false`.*
:::

:::proofen
Work backwards, on the right side: `rw [← coin_and]` uses the rule from right to left, and
`rw [← coin_not]` turns `coin (σ p)` into `not <$> coin p`. Then a gate sits inside the `do` block,
in `let y ← not <$> coin p`. The new rule
`bind_map_left : (do let x ← f <$> μ; g x) = (do let x ← μ; g (f x))` takes the gate out of the draw
and into what is computed. But it is needed after `let x ← coin p`, where the name `x` of the `do`
block occurs, and there `rw` cannot rewrite. The new tactic `simp only [rules]` can: it rewrites with
the rules everywhere, also inside `do` blocks, as often as it can, and closes the goal when the two
sides become the same.

*Tip.* `rw [← coin_and]`, `rw [← coin_not]`, `simp only [bind_map_left]`.
:::

:::proofde
Arbeite rückwärts, auf der rechten Seite: `rw [← coin_and]` benutzt die Regel von rechts nach
links, und `rw [← coin_not]` macht aus `coin (σ p)` ein `not <$> coin p`. Dann steht ein Baustein im
`do`-Block, in `let y ← not <$> coin p`. Die neue Regel
`bind_map_left : (do let x ← f <$> μ; g x) = (do let x ← μ; g (f x))` holt den Baustein aus dem Ziehen
heraus und in das Rechnen hinein. Gebraucht wird sie aber nach `let x ← coin p`, wo der Name `x` des
`do`-Blocks vorkommt, und dort kann `rw` nicht umschreiben. Die neue Taktik `simp only [Regeln]` kann
es: Sie schreibt mit den Regeln überall um, auch in `do`-Blöcken, so oft es geht, und schließt das
Ziel, wenn beide Seiten gleich werden.

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

::::leanonly (proof := "(p : I) (f : Bool → DiscreteMeasure Bool) : not <$> (coin p >>= f) = coin p >>= (fun x => not <$> f x)") (new := "map_bind")
:::en
*A move after a draw.* A move at the end can go into the `do` block.
:::

:::de
*Ein Zug nach dem Ziehen.* Ein Zug am Ende kann in den `do`-Block hinein.
:::

:::proofen
`map_bind : f <$> (μ >>= g) = μ >>= fun x => f <$> g x`.

*Tip.* `rw [map_bind]`.
:::

:::proofde
`map_bind : f <$> (μ >>= g) = μ >>= fun x => f <$> g x`.

*Tipp.* `rw [map_bind]`.
:::
:::solution
```
rw [map_bind]
```
:::
::::

::::leanonly (proof := "(p : I) : (do let _ ← coin p; pure true) = (pure true : DiscreteMeasure Bool)") (new := "coin_unused")
:::en
*An unused coin.* A coin whose outcome is not used changes nothing.
:::

:::de
*Eine unbenutzte Münze.* Eine Münze, deren Ergebnis nicht benutzt wird, ändert nichts.
:::

:::proofen
`coin_unused : (do let _ ← coin p; ν) = ν` (`_`: the outcome gets no name, it is not used).

*Tip.* `rw [coin_unused]`.
:::

:::proofde
`coin_unused : (do let _ ← coin p; ν) = ν` (`_`: Das Ergebnis bekommt keinen Namen, es wird nicht benutzt).

*Tipp.* `rw [coin_unused]`.
:::
:::solution
```
rw [coin_unused]
```
:::
::::

::::circuit (inputs := "x y") (gates := "and, or, not") (coins := "p p") (target := "bool true:2p(1-p) false:p^2+(1-p)^2") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure ((x || y) && !(x && y))) = (do let x ← coin p; let y ← coin p; pure (xor x y))") (play := "a=or; b=and; c=not; d=and; x>a.0; y>a.1; x>b.0; y>b.1; b>c.0; a>d.0; c>d.1; d>out")
:::en
*Boss: exactly one `true`*, without a function for it: at least one, but not both.
:::

:::de
*Endgegner: genau einmal `true`*, ohne eine Funktion dafür: mindestens einmal, aber nicht beide.
:::

:::proofen
*Boss.* Exactly one `true` is `xor`. Both sides throw the same coins; go under the throws, with `congr 1`
and `funext x` (and again for `y`), and look at all four cases, with `<;>` in one line.

*Tip.* `congr 1`, `funext x`, `congr 1`, `funext y`, `cases x <;> cases y <;> rfl`.
:::

:::proofde
*Endgegner.* Genau einmal `true` ist `xor`. Beide Seiten werfen dieselben Münzen; geh unter die Würfe, mit
`congr 1` und `funext x` (und nochmal für `y`), und sieh dir alle vier Fälle an, mit `<;>` in einer Zeile.

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
