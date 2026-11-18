import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Maps" =>

%%%
htmlSplit := .never
%%%

:::en
Maps on `Bool`, and moves with them. There are exactly four maps `Bool → Bool`: `id`, `not`, always
`true` (`fun _ => true`) and always `false` (`fun _ => false`). A statement about an unknown map
`f : Bool → Bool` holds for every map when it holds for each of the four.
:::

:::de
Abbildungen auf `Bool`, und Züge mit ihnen. Es gibt genau vier Abbildungen `Bool → Bool`: `id`,
`not`, immer `true` (`fun _ => true`) und immer `false` (`fun _ => false`). Eine Aussage über eine
unbekannte Abbildung `f : Bool → Bool` gilt für jede Abbildung, wenn sie für jede der vier gilt.
:::

::::leanonly (proof := "(f : Bool → Bool) (b : Bool) : f (f (f b)) = f b") (lemma := "Bool.apply_apply_apply") (new := "decide") (group := "bool") (uses := "-")
:::en
*Three times is once.* Whatever map `f : Bool → Bool` is, applied three times it does the same as
once: `f (f (f b)) = f b`. Check it for `not`: three times `not` is `not`; and for always `true`. In Lean the new tactic `decide` checks it, in every case at once.
:::

:::de
*Dreimal ist einmal.* Welche Abbildung `f : Bool → Bool` auch immer: dreimal angewandt tut sie
dasselbe wie einmal, `f (f (f b)) = f b`. Prüf es für `not`: dreimal `not` ist `not`; und für immer
`true`. In Lean prüft es die neue Taktik `decide`, in allen Fällen auf einmal.
:::

:::proofen
No rule says what `f` does, so there is nothing to rewrite, and no `rw` here. But there are only four maps `Bool → Bool`, `id`, `not` and the two constant ones, and with
the two values of `b` these are eight cases. The new tactic `decide` reduces a statement about finitely
many cases until it is `true` or `false`; `decide +revert` first takes the variables into the
statement, here `∀ f b, …`, and so checks every case. With
coins this no longer works: a coin `coin p` is a different distribution for every number `p` between
0 and 1, infinitely many cases. There, the rules do the work, and this lemma: it is unlocked as
`Bool.apply_apply_apply`.

*Tip.* `decide +revert`.
:::

:::proofde
Keine Regel sagt, was `f` tut; es gibt also nichts umzuschreiben, und hier kein `rw`. Aber es gibt nur vier Abbildungen `Bool → Bool`, `id`, `not` und die
zwei konstanten, und mit den zwei Werten von `b` sind das acht Fälle. Die neue Taktik `decide`
reduziert eine Aussage über endlich viele Fälle, bis sie `true` oder `false` ist; `decide +revert`
nimmt zuerst die Variablen in die Aussage, hier `∀ f b, …`, und prüft so jeden Fall. Mit
Münzen geht das nicht mehr: Eine Münze `coin p` ist für jede Zahl `p`
zwischen 0 und 1 eine andere Verteilung, unendlich viele Fälle. Dort machen die Regeln die Arbeit, und
dieses Lemma: Es wird als `Bool.apply_apply_apply` freigeschaltet.

*Tipp.* `decide +revert`.
:::
:::solution
```
decide +revert
```
:::
::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) : (μ.map not).map not = μ.map (fun x => !(!x))") (new := "map_map") (uses := "map_map")
:::en
*Two moves are one.* Two moves one after the other are one move: the composed map.
:::

:::de
*Zwei Züge sind einer.* Zwei Züge nacheinander sind ein Zug: die zusammengesetzte Abbildung.
:::

:::proofen
`map_map : (μ.map f).map g = μ.map (fun x => g (f x))`.

*Tip.* `rw [map_map]`.
:::

:::proofde
`map_map : (μ.map f).map g = μ.map (fun x => g (f x))`.

*Tipp.* `rw [map_map]`.
:::
:::solution
```
rw [map_map]
```
:::
::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) : (μ.map not).map not = μ") (new := "simp_rw, map_id") (uses := "map_map, Bool.not_not, map_id")
:::en
*Turned over twice.* Turning the coin over twice does nothing: `(μ.map not).map not = μ`.
:::

:::de
*Zweimal umgedreht.* Zweimal umdrehen tut nichts: `(μ.map not).map not = μ`.
:::

:::proofen
`rw [map_map]` makes the two moves one, `μ.map (fun x => !(!x))`. Your lemma from *Circuits*,
`Bool.not_not : (!(!b)) = b`, should make `!(!x)` into `x`. But `rw [Bool.not_not]` does not find
`!(!x)`, though it stands there: the `x` in `fun x => …` is a *bound* name, like the index `x` of a
sum `∑ x, …`, and `rw` rewrites only parts without bound names. The new tactic `simp_rw [rules]` is
`rw`, also under bound names. Then the move does nothing: `map_id : μ.map (fun x => x) = μ`.

*Tip.* `rw [map_map]`, `simp_rw [Bool.not_not]`, `rw [map_id]`.
:::

:::proofde
`rw [map_map]` macht aus den zwei Zügen einen, `μ.map (fun x => !(!x))`. Dein Lemma aus
*Schaltungen*, `Bool.not_not : (!(!b)) = b`, soll aus `!(!x)` ein `x` machen. Aber `rw [Bool.not_not]`
findet `!(!x)` nicht, obwohl es dasteht: Das `x` in `fun x => …` ist ein *gebundener* Name, wie der
Index `x` einer Summe `∑ x, …`, und `rw` schreibt nur Teile ohne gebundene Namen um. Die neue Taktik
`simp_rw [Regeln]` ist `rw`, auch unter gebundenen Namen. Dann tut der Zug nichts:
`map_id : μ.map (fun x => x) = μ`.

*Tipp.* `rw [map_map]`, `simp_rw [Bool.not_not]`, `rw [map_id]`.
:::
:::solution
```
rw [map_map]
simp_rw [Bool.not_not]
rw [map_id]
```
:::
::::

::::leanonly (proof := "(f : Bool → Bool) (p : I) : (((coin p).map f).map f).map f = (coin p).map f") (new := "congr, funext") (uses := "map_map, Bool.apply_apply_apply")
:::en
*Three times is once, with a coin.* The same, now on a coin: three moves with `f` move the coin as
one move with `f` does.
:::

:::de
*Dreimal ist einmal, mit einer Münze.* Dasselbe, jetzt auf einer Münze: Drei Züge mit `f` bewegen
die Münze wie ein Zug mit `f`.
:::

:::proofen
Three moves one after the other are one move: the rule
`map_map : (μ.map f).map g = μ.map (fun x => g (f x))`, twice. Then both sides move the same coin,
with two maps. Two new tactics: `congr 1` reduces the goal to the two maps being equal, and `funext b`
to their being equal at every point `b`. That is the lemma of the first level of this world:
`exact Bool.apply_apply_apply f b`.

*Tip.* `rw [map_map, map_map]`, `congr 1`, `funext b`, `exact Bool.apply_apply_apply f b`.
:::

:::proofde
Drei Züge hintereinander sind ein Zug: die Regel
`map_map : (μ.map f).map g = μ.map (fun x => g (f x))`, zweimal. Dann bewegen beide Seiten dieselbe
Münze, mit zwei Abbildungen. Zwei neue Taktiken: `congr 1` führt das Ziel darauf zurück, dass die
beiden Abbildungen gleich sind, und `funext b` darauf, dass sie an jeder Stelle `b` gleich sind. Das
ist das Lemma des ersten Levels dieser Welt: `exact Bool.apply_apply_apply f b`.

*Tipp.* `rw [map_map, map_map]`, `congr 1`, `funext b`, `exact Bool.apply_apply_apply f b`.
:::
:::solution
```
rw [map_map, map_map]
congr 1
funext b
exact Bool.apply_apply_apply f b
```
:::
::::
