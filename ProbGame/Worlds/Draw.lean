import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Draw, then Compute" =>

%%%
htmlSplit := .never
%%%

:::en
A move `f <$> μ` is two steps: first *draw* from `μ`, then *compute* with what was drawn. In Lean this
is a `do` block, `do let x ← μ; pure (f x)`: `let x ← μ` draws `x` from the distribution `μ`, and
`pure` gives back a sure result. The board is the one of *One Coin*. The proofs learn the rules of
`do` blocks, the *monad laws*; with them, the circuits of the next world become proofs.
:::

:::de
Ein Zug `f <$> μ` besteht aus zwei Schritten: Zuerst wird aus `μ` *gezogen*, dann mit dem Gezogenen
*gerechnet*. In Lean ist das ein `do`-Block, `do let x ← μ; pure (f x)`: `let x ← μ` zieht `x` aus der
Verteilung `μ`, und `pure` gibt ein sicheres Ergebnis zurück. Das Spielfeld ist das aus *Eine Münze*.
Die Beweise lernen die Regeln der `do`-Blöcke, die *Monadengesetze*; mit ihnen werden die Schaltpläne
der nächsten Welt zu Beweisen.
:::

::::level (start := "bernoulli p") (target := "bernoulli 1-p") (moves := "not") (lean := "(do let x ← coin p; pure (!x)) = coin (σ p)") (leanTarget := "coin (σ p)") (no := "2.1") (proof := "(p : I) : (do let x ← coin p; pure (!x)) = not <$> coin p")
:::en
*A move is a draw.* Flip the coin.
:::

:::de
*Ein Zug ist ein Ziehen.* Dreh die Münze um.
:::

:::proofen
`do let x ← coin p; pure (!x)` draws `x` from the coin and gives back `!x`: that is the move `not`.
The rule `map_eq_pure_bind : f <$> μ = do let x ← μ; pure (f x)` says so for every move.

*Tip.* `rw [map_eq_pure_bind]`.
:::

:::proofde
`do let x ← coin p; pure (!x)` zieht `x` aus der Münze und gibt `!x` zurück: Das ist der Zug `not`.
Die Regel `map_eq_pure_bind : f <$> μ = do let x ← μ; pure (f x)` sagt das für jeden Zug.

*Tipp.* `rw [map_eq_pure_bind]`.
:::
::::

::::level (start := "pure true") (target := "pure false") (moves := "not") (lean := "(do let x ← pure true; pure (!x)) = pure false") (leanStart := "DiscreteMeasure.pure true") (leanTarget := "DiscreteMeasure.pure false") (no := "2.2") (proof := ": (do let x ← pure true; pure (!x)) = (pure false : DiscreteMeasure Bool)")
:::en
*A sure draw.* The coin lies surely on `true`: all the sand is there, a point mass, `pure true` in
Lean. Flip it.
:::

:::de
*Ein sicheres Ziehen.* Die Münze liegt sicher auf `true`: Der ganze Sand liegt dort, eine Punktmasse,
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
::::

::::level (start := "bernoulli p") (target := "bernoulli p") (moves := "id, not") (count := "1") (lean := "(coin p >>= fun x => pure x) = coin p") (leanTarget := "coin p") (no := "2.3") (proof := "(p : I) : (coin p >>= fun x => pure x) = coin p")
:::en
*Drawn, and given back.* Leave the coin as it is, with one move.
:::

:::de
*Gezogen und zurückgegeben.* Lass die Münze, wie sie ist, mit einem Zug.
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
::::

::::level (start := "bernoulli p") (target := "bernoulli p") (moves := "not") (lean := "(do let y ← (do let x ← coin p; pure (!x)); pure (!y)) = coin p") (leanTarget := "coin p") (no := "2.4") (proof := "(p : I) : (do let y ← (do let x ← coin p; pure (!x)); pure (!y)) = coin p")
:::en
*Two moves, one draw.* Flip twice.
:::

:::de
*Zwei Züge, ein Ziehen.* Zweimal umdrehen.
:::

:::proofen
Two moves are a `do` block inside a `do` block. `bind_assoc` makes them one:
`(do let y ← (do let x ← μ; f x); g y) = (do let x ← μ; let y ← f x; g y)`. Then `pure_bind` is
needed after `let x ← coin p`, where the name `x` of the `do` block occurs, and there `rw` cannot
rewrite. The new tactic `simp only [rules]` can: it rewrites with the rules everywhere, also inside
`do` blocks, as often as it can, and closes the goal when the two sides become the same. Your
`Bool.not_not` from *True and False* is in the inventory.

*Tip.* `rw [bind_assoc]`, `simp only [pure_bind, Bool.not_not]`, `rw [bind_pure]`.
:::

:::proofde
Zwei Züge sind ein `do`-Block in einem `do`-Block. `bind_assoc` macht einen daraus:
`(do let y ← (do let x ← μ; f x); g y) = (do let x ← μ; let y ← f x; g y)`. Dann wird `pure_bind`
nach `let x ← coin p` gebraucht, wo der Name `x` des `do`-Blocks vorkommt, und dort kann `rw` nicht
umschreiben. Die neue Taktik `simp only [Regeln]` kann es: Sie schreibt mit den Regeln überall um,
auch in `do`-Blöcken, so oft es geht, und schließt das Ziel, wenn beide Seiten gleich werden. Dein
`Bool.not_not` aus *Wahr und falsch* ist im Inventar.

*Tipp.* `rw [bind_assoc]`, `simp only [pure_bind, Bool.not_not]`, `rw [bind_pure]`.
:::
::::

::::level (start := "bernoulli 1-p") (target := "bernoulli p") (moves := "not") (lean := "(do let x ← not <$> coin p; pure (!x)) = coin p") (leanStart := "(coin p).map not") (leanTarget := "coin p") (no := "2.5") (proof := "(p : I) : (do let x ← not <$> coin p; pure (!x)) = coin p")
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
`bind_map_left : (do let x ← f <$> μ; g x) = (do let x ← μ; g (f x))` takes the move out of the draw
and into what is computed.

*Tip.* `rw [bind_map_left]`, `simp only [Bool.not_not]`, `rw [bind_pure]`.
:::

:::proofde
Hier wird aus `not <$> coin p` gezogen. Die Regel
`bind_map_left : (do let x ← f <$> μ; g x) = (do let x ← μ; g (f x))` holt den Zug aus dem Ziehen
heraus und in das Rechnen hinein.

*Tipp.* `rw [bind_map_left]`, `simp only [Bool.not_not]`, `rw [bind_pure]`.
:::
::::

::::level (start := "bernoulli p") (target := "pure true") (moves := "not, heads") (lean := "(do let _ ← coin p; pure true) = pure true") (leanTarget := "DiscreteMeasure.pure true") (no := "2.6") (proof := "(p : I) (b : Bool) : (do let _ ← coin p; pure b) = pure b")
:::en
*A draw that is not used.* Lay the coin surely on `true`.
:::

:::de
*Ein Ziehen, das nicht gebraucht wird.* Leg die Münze sicher auf `true`.
:::

:::proofen
`do let _ ← coin p; pure b` draws, but forgets what it drew (`_`), and gives back `b`. Read from right
to left, `map_eq_pure_bind` makes it a move, `(fun _ => b) <$> coin p`, and that is your `coin_const`.

*Tip.* `rw [← map_eq_pure_bind]`, then `rw [coin_const]`.
:::

:::proofde
`do let _ ← coin p; pure b` zieht, vergisst aber das Gezogene (`_`) und gibt `b` zurück. Von rechts
nach links gelesen macht `map_eq_pure_bind` daraus einen Zug, `(fun _ => b) <$> coin p`, und das ist
dein `coin_const`.

*Tipp.* `rw [← map_eq_pure_bind]`, dann `rw [coin_const]`.
:::
::::

::::level (start := "bernoulli p") (target := "bernoulli 1-p") (moves := "not") (count := "3") (lean := "(do let y ← (do let x ← coin p; pure (!x)); let z ← pure (!y); pure (!z)) = not <$> coin p") (leanTarget := "coin (σ p)") (no := "2.7") (proof := "(p : I) : (do let y ← (do let x ← coin p; pure (!x)); let z ← pure (!y); pure (!z)) = not <$> coin p")
:::en
*The boss: three flips.* Flip the coin three times.
:::

:::de
*Der Endgegner: dreimal umdrehen.* Dreh die Münze dreimal um.
:::

:::proofen
A `do` block in a `do` block, and a sure draw after it: all the rules of this world. In the end, the
`do` block is a move again.

*Tip.* `rw [bind_assoc]`, `simp only [pure_bind, Bool.not_not]`, `rw [map_eq_pure_bind]`.
:::

:::proofde
Ein `do`-Block in einem `do`-Block und danach ein sicheres Ziehen: alle Regeln dieser Welt. Am Ende
ist der `do`-Block wieder ein Zug.

*Tipp.* `rw [bind_assoc]`, `simp only [pure_bind, Bool.not_not]`, `rw [map_eq_pure_bind]`.
:::
::::
