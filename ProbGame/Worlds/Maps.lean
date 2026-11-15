import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Maps" =>

%%%
htmlSplit := .never
%%%

:::en
There are exactly four maps `Bool → Bool`: `id`, `not`, always `T` (`fun _ => true`) and always `F`
(`fun _ => false`). A new gate, `f`, is an unknown map: it has a field for a map, and every `f` on the
board has the same one. Drag a map into the field, or tap the field until it is the one you want.
A statement about `f` holds for every map when it holds for each of the four: try them all.
:::

:::de
Es gibt genau vier Abbildungen `Bool → Bool`: `id`, `not`, immer `T` (`fun _ => true`) und immer `F`
(`fun _ => false`). Ein neuer Baustein, `f`, ist eine unbekannte Abbildung: Er hat ein Feld für eine
Abbildung, und jedes `f` auf dem Spielfeld hat dieselbe. Zieh eine Abbildung ins Feld, oder tippe das
Feld an, bis es die richtige ist. Eine Aussage über `f` gilt für jede Abbildung, wenn sie für jede der
vier gilt: Probier sie alle aus.
:::

::::circuit (inputs := "b") (gates := "") (table := "f") (shape := "f (f (f b))") (start := "a=f; c=f; d=f; b>a.0; a>c.0; c>d.0; d>out") (proof := "(f : Bool → Bool) (b : Bool) : f (f (f b)) = f b") (lemma := "Bool.apply_apply_apply") (new := "decide") (play := "a.0=id")
:::en
*Three times is once.* The circuit `f (f (f b))` is there; the target is `f` itself, once. Choose a
map in `f`, and then another: for each of the four, three times is the same as once.
:::

:::de
*Dreimal ist einmal.* Die Schaltung `f (f (f b))` liegt da; das Ziel ist `f` selbst, einmal. Wähle
eine Abbildung in `f`, und dann eine andere: Für jede der vier ist dreimal dasselbe wie einmal.
:::

:::proofen
No rule says what `f` does. But there are only four maps `Bool → Bool`, the four you tried, and with
the two values of `b` these are eight cases. The new tactic `decide` reduces a statement about finitely
many cases until it is `true` or `false`; `decide +revert` first takes the variables into the
statement, here `∀ f b, …`, and so checks every case, as the board did. With
coins this no longer works: a coin `coin p` is a different distribution for every number `p` between
0 and 1, infinitely many cases. There, the rules do the work, and this lemma: it is unlocked as
`Bool.apply_apply_apply`.

*Tip.* `decide +revert`.
:::

:::proofde
Keine Regel sagt, was `f` tut. Aber es gibt nur vier Abbildungen `Bool → Bool`, die vier, die du
ausprobiert hast, und mit den zwei Werten von `b` sind das acht Fälle. Die neue Taktik `decide`
reduziert eine Aussage über endlich viele Fälle, bis sie `true` oder `false` ist; `decide +revert`
nimmt zuerst die Variablen in die Aussage, hier `∀ f b, …`, und prüft so jeden Fall, wie das
Spielfeld. Mit Münzen geht das nicht mehr: Eine Münze `coin p` ist für jede Zahl `p`
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

::::leanonly (proof := "(μ : DiscreteMeasure Bool) : not <$> (not <$> μ) = (fun x => !(!x)) <$> μ") (new := "map_map")
:::en
*Two moves are one.* Two moves one after the other are one move: the composed map.
:::

:::de
*Zwei Züge sind einer.* Zwei Züge nacheinander sind ein Zug: die zusammengesetzte Abbildung.
:::

:::proofen
`map_map : g <$> (f <$> μ) = (fun x => g (f x)) <$> μ`.

*Tip.* `rw [map_map]`.
:::

:::proofde
`map_map : g <$> (f <$> μ) = (fun x => g (f x)) <$> μ`.

*Tipp.* `rw [map_map]`.
:::
:::solution
```
rw [map_map]
```
:::
::::

::::circuit (inputs := "x") (gates := "") (coins := "p") (target := "f bernoulli p") (start := "a=f; c=f; d=f; x>a.0; a>c.0; c>d.0; d>out") (context := "Lean/Rules.lean") (proof := "(f : Bool → Bool) (p : I) : f <$> (f <$> (f <$> coin p)) = f <$> coin p") (new := "congr, funext") (play := "a.0=id")
:::en
*Three times is once, with a coin.* The same circuit, now on a coin `x ← coin p`; the target is the
distribution of `f x`, once. Choose a map in `f`, and then another.
:::

:::de
*Dreimal ist einmal, mit einer Münze.* Dieselbe Schaltung, jetzt auf einer Münze `x ← coin p`; das
Ziel ist die Verteilung von `f x`, einmal. Wähle eine Abbildung in `f`, und dann eine andere.
:::

:::proofen
Three gates one after the other are one gate: the new rule
`map_map : g <$> (f <$> μ) = (fun x => g (f x)) <$> μ`, twice. Then both sides move the same coin,
with two maps. Two new tactics: `congr 1` reduces the goal to the two maps being equal, and `funext b`
to their being equal at every point `b`. That is the lemma of the level before:
`exact Bool.apply_apply_apply f b`.

*Tip.* `rw [map_map, map_map]`, `congr 1`, `funext b`, `exact Bool.apply_apply_apply f b`.
:::

:::proofde
Drei Bausteine hintereinander sind ein Baustein: die neue Regel
`map_map : g <$> (f <$> μ) = (fun x => g (f x)) <$> μ`, zweimal. Dann bewegen beide Seiten dieselbe
Münze, mit zwei Abbildungen. Zwei neue Taktiken: `congr 1` führt das Ziel darauf zurück, dass die
beiden Abbildungen gleich sind, und `funext b` darauf, dass sie an jeder Stelle `b` gleich sind. Das
ist das Lemma des Levels davor: `exact Bool.apply_apply_apply f b`.

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
