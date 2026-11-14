import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Draw, then Compute" =>

%%%
htmlSplit := .never
%%%

:::en
A gate on a coin, `f <$> μ`, is two steps: first *draw* from `μ`, then *compute* with what was drawn.
In Lean this is a `do` block, `do let x ← μ; pure (f x)`: `let x ← μ` draws `x` from the distribution
`μ`, and `pure` gives back a sure result. Without the words of `do`, the same reads
`μ >>= fun x => pure (f x)`: `>>=` (*bind*) passes what `μ` drew to the function after it, and
`fun x => …` is that function. The board is the one of *One Coin*, read from top to bottom: the line
`x ← coin p` at the top is `let x ← coin p`, and what the gates compute is the `pure (…)` at the end. The proofs learn the rules of
`do` blocks, the *monad laws*; with them, the circuits of the next world become proofs.
:::

:::de
Ein Baustein auf einer Münze, `f <$> μ`, besteht aus zwei Schritten: Zuerst wird aus `μ` *gezogen*, dann
mit dem Gezogenen *gerechnet*. In Lean ist das ein `do`-Block, `do let x ← μ; pure (f x)`: `let x ← μ`
zieht `x` aus der Verteilung `μ`, und `pure` gibt ein sicheres Ergebnis zurück. Ohne die Wörter von `do`
liest sich dasselbe `μ >>= fun x => pure (f x)`: `>>=` (*bind*) gibt, was `μ` gezogen hat, an die
Funktion danach weiter, und `fun x => …` ist diese Funktion. Das Spielfeld ist das aus *Eine Münze*,
von oben nach unten gelesen: die Zeile `x ← coin p` oben ist `let x ← coin p`, und was die Bausteine
rechnen, ist das `pure (…)` am Ende.
Die Beweise lernen die Regeln der `do`-Blöcke, die *Monadengesetze*; mit ihnen werden die Schaltpläne
der nächsten Welt zu Beweisen.
:::

::::circuit (inputs := "x") (gates := "not") (coins := "p") (target := "bernoulli 1-p") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; pure (!x)) = not <$> coin p") (new := "map_eq_pure_bind") (play := "a=not; x>a.0; a>out")
:::en
*A gate is a draw.* Flip the coin: a `not` between the coin and the output.
:::

:::de
*Ein Baustein ist ein Ziehen.* Dreh die Münze um: ein `nicht` zwischen Münze und Ausgang.
:::

:::proofen
`do let x ← coin p; pure (!x)` draws `x` from the coin and gives back `!x`: that is the gate `not`.
The rule `map_eq_pure_bind : f <$> μ = do let x ← μ; pure (f x)` says so for every gate (every map).

*Tip.* `rw [map_eq_pure_bind]`.
:::

:::proofde
`do let x ← coin p; pure (!x)` zieht `x` aus der Münze und gibt `!x` zurück: Das ist der Baustein `not`.
Die Regel `map_eq_pure_bind : f <$> μ = do let x ← μ; pure (f x)` sagt das für jeden Baustein (jede Abbildung).

*Tipp.* `rw [map_eq_pure_bind]`.
:::
:::solution
```
rw [map_eq_pure_bind]
```
:::
::::

::::circuit (inputs := "x") (gates := "not") (coins := "1") (target := "pure false") (context := "Lean/Rules.lean") (proof := ": (do let x ← pure true; pure (!x)) = (pure false : DiscreteMeasure Bool)") (new := "pure_bind") (play := "a=not; x>a.0; a>out")
:::en
*A sure draw.* The coin lies surely on `true`: all the mass is there, a point mass, `pure true` in
Lean. Flip it.
:::

:::de
*Ein sicheres Ziehen.* Die Münze liegt sicher auf `true`: Die ganze Masse liegt dort, eine Punktmasse,
in Lean `pure true`. Dreh sie um.
:::

:::proofen
Drawing from `pure a` always gives `a`: `pure_bind : (do let x ← pure a; f x) = f a`. What is left
is computing.

*Tip.* `rw [pure_bind]`, then `rw [Bool.not_true]`.
:::

:::proofde
Aus `pure a` zieht man immer `a`: `pure_bind : (do let x ← pure a; f x) = f a`. Was bleibt, ist
Rechnen.

*Tipp.* `rw [pure_bind]`, dann `rw [Bool.not_true]`.
:::
:::solution
```
rw [pure_bind]
rw [Bool.not_true]
```
:::
::::

::::circuit (inputs := "x") (gates := "not") (coins := "p") (target := "bernoulli p") (context := "Lean/Rules.lean") (proof := "(p : I) : (coin p >>= fun x => pure x) = coin p") (new := "bind_pure") (play := "x>out")
:::en
*Drawn, and given back.* Leave the coin as it is: a wire from the coin to the output, no gate.
:::

:::de
*Gezogen und zurückgegeben.* Lass die Münze, wie sie ist: ein Draht von der Münze zum Ausgang, kein Baustein.
:::

:::proofen
Without `do`, a draw is written with `>>=` (*bind*): `μ >>= f` draws from `μ` and goes on with `f`;
`do let x ← μ; f x` is `μ >>= fun x => f x`. To draw and give back what was drawn changes nothing:
`bind_pure : (μ >>= fun x => pure x) = μ`. (In a `do` block, Lean shortens `let x ← μ; pure x` to `μ`
at once; so here the statement is written with `>>=`.)

*Tip.* `rw [bind_pure]`.
:::

:::proofde
Ohne `do` schreibt man ein Ziehen mit `>>=` (*bind*): `μ >>= f` zieht aus `μ` und macht mit `f`
weiter; `do let x ← μ; f x` ist `μ >>= fun x => f x`. Ziehen und das Gezogene zurückgeben ändert
nichts: `bind_pure : (μ >>= fun x => pure x) = μ`. (In einem `do`-Block kürzt Lean
`let x ← μ; pure x` sofort zu `μ`; deshalb steht die Aussage hier mit `>>=`.)

*Tipp.* `rw [bind_pure]`.
:::
:::solution
```
rw [bind_pure]
```
:::
::::

::::circuit (inputs := "x") (gates := "not") (coins := "p") (target := "bernoulli p") (start := "a=not; x>a.0") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let y ← (do let x ← coin p; pure (!x)); pure (!y)) = coin p") (new := "simp only, bind_assoc") (play := "b=not; a>b.0; b>out")
:::en
*Two gates, one draw.* Flip twice; the first `not` is there already.
:::

:::de
*Zwei Bausteine, ein Ziehen.* Zweimal umdrehen; das erste `nicht` liegt schon da.
:::

:::proofen
Two gates are a `do` block inside a `do` block. `bind_assoc` makes them one:
`(do let y ← (do let x ← μ; f x); g y) = (do let x ← μ; let y ← f x; g y)`. Then `pure_bind` is
needed after `let x ← coin p`, where the name `x` of the `do` block occurs, and there `rw` cannot
rewrite. The new tactic `simp only [rules]` can: it rewrites with the rules everywhere, also inside
`do` blocks, as often as it can, and closes the goal when the two sides become the same. Your
`Bool.not_not` from *Circuits* is in the inventory.

*Tip.* `rw [bind_assoc]`, `simp only [pure_bind, Bool.not_not]`, `rw [bind_pure]`.
:::

:::proofde
Zwei Bausteine sind ein `do`-Block in einem `do`-Block. `bind_assoc` macht einen daraus:
`(do let y ← (do let x ← μ; f x); g y) = (do let x ← μ; let y ← f x; g y)`. Dann wird `pure_bind`
nach `let x ← coin p` gebraucht, wo der Name `x` des `do`-Blocks vorkommt, und dort kann `rw` nicht
umschreiben. Die neue Taktik `simp only [Regeln]` kann es: Sie schreibt mit den Regeln überall um,
auch in `do`-Blöcken, so oft es geht, und schließt das Ziel, wenn beide Seiten gleich werden. Dein
`Bool.not_not` aus *Schaltungen* ist im Inventar.

*Tipp.* `rw [bind_assoc]`, `simp only [pure_bind, Bool.not_not]`, `rw [bind_pure]`.
:::
:::solution
```
rw [bind_assoc]
simp only [pure_bind, Bool.not_not]
rw [bind_pure]
```
:::
::::

::::circuit (inputs := "x") (gates := "not") (coins := "1-p") (target := "bernoulli p") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← not <$> coin p; pure (!x)) = coin p") (new := "bind_map_left") (play := "a=not; x>a.0; a>out")
:::en
*Drawn from a flipped coin.* This coin is flipped already: `true` has the mass $`1 - p`. Flip it
back.
:::

:::de
*Aus einer umgedrehten Münze gezogen.* Diese Münze ist schon umgedreht: `true` hat die Masse
$`1 - p`. Dreh sie zurück.
:::

:::proofen
Here the draw is from `not <$> coin p`. The rule
`bind_map_left : (do let x ← f <$> μ; g x) = (do let x ← μ; g (f x))` takes the gate out of the draw
and into what is computed.

*Tip.* `rw [bind_map_left]`, `simp only [Bool.not_not]`, `rw [bind_pure]`.
:::

:::proofde
Hier wird aus `not <$> coin p` gezogen. Die Regel
`bind_map_left : (do let x ← f <$> μ; g x) = (do let x ← μ; g (f x))` holt den Baustein aus dem Ziehen
heraus und in das Rechnen hinein.

*Tipp.* `rw [bind_map_left]`, `simp only [Bool.not_not]`, `rw [bind_pure]`.
:::
:::solution
```
rw [bind_map_left]
simp only [Bool.not_not]
rw [bind_pure]
```
:::
::::

::::circuit (inputs := "x") (gates := "not, alwaysT") (coins := "p") (target := "pure true") (context := "Lean/Rules.lean") (proof := "(p : I) (b : Bool) : (do let _ ← coin p; pure b) = pure b") (play := "a=alwaysT; x>a.0; a>out")
:::en
*A draw that is not used.* Lay the coin surely on `true`.
:::

:::de
*Ein Ziehen, das nicht gebraucht wird.* Leg die Münze sicher auf `true`.
:::

:::proofen
`do let _ ← coin p; pure b` draws, but forgets what it drew (`_`), and gives back `b`. Read from right
to left, `map_eq_pure_bind` makes it a gate, `(fun _ => b) <$> coin p`, and that is your `coin_const`.

*Tip.* `rw [← map_eq_pure_bind]`, then `rw [coin_const]`.
:::

:::proofde
`do let _ ← coin p; pure b` zieht, vergisst aber das Gezogene (`_`) und gibt `b` zurück. Von rechts
nach links gelesen macht `map_eq_pure_bind` daraus einen Baustein, `(fun _ => b) <$> coin p`, und das ist
dein `coin_const`.

*Tipp.* `rw [← map_eq_pure_bind]`, dann `rw [coin_const]`.
:::
:::solution
```
rw [← map_eq_pure_bind]
rw [coin_const]
```
:::
::::

::::circuit (inputs := "x") (gates := "not") (coins := "p") (target := "bernoulli 1-p") (start := "a=not; b=not; x>a.0; a>b.0") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let y ← (do let x ← coin p; pure (!x)); let z ← pure (!y); pure (!z)) = coin (σ p)") (play := "c=not; b>c.0; c>out")
:::en
*The boss: three flips.* Flip the coin three times; two `not` are there already.
:::

:::de
*Der Endgegner: dreimal umdrehen.* Dreh die Münze dreimal um; zwei `nicht` liegen schon da.
:::

:::proofen
A `do` block in a `do` block, and a sure draw after it: all the rules of this world, and the boss of
*One Coin*. In the end, the `do` block is a gate again (`map_eq_pure_bind` from right to left), and the
flipped coin is the coin $`1 - p`.

*Tip.* `rw [bind_assoc]`, `simp only [pure_bind, Bool.not_not]`, `rw [← map_eq_pure_bind]`, `rw [coin_not]`.
:::

:::proofde
Ein `do`-Block in einem `do`-Block und danach ein sicheres Ziehen: alle Regeln dieser Welt, und der
Endgegner von *Eine Münze*. Am Ende ist der `do`-Block wieder ein Baustein (`map_eq_pure_bind` von rechts
nach links), und die umgedrehte Münze ist die Münze $`1 - p`.

*Tipp.* `rw [bind_assoc]`, `simp only [pure_bind, Bool.not_not]`, `rw [← map_eq_pure_bind]`, `rw [coin_not]`.
:::
:::solution
```
rw [bind_assoc]
simp only [pure_bind, Bool.not_not]
rw [← map_eq_pure_bind]
rw [coin_not]
```
:::
::::
