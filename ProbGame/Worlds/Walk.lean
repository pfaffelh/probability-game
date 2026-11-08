import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Walking on the Grid" =>

%%%
htmlSplit := .never
number := false
%%%

:::en
Before chance comes in: a figure walks on the grid $`\mathbb{Z} \times \mathbb{Z}`, and every move is
sure. A move is a map `north : Pos → m Pos` into a *monad* `m`, and a walk is a program:
`pure (0, 0) >>= north >>= east` starts at $`(0, 0)`, goes north, then east. First the monad is `Id`,
the monad of sure results: the walk ends at one point. Then it is `Set`: a move may go several ways,
and the walk ends in the set of the points it can reach. In the worlds after this one the monad is
that of distributions, and a move goes each way with a probability.
:::

:::de
Bevor der Zufall kommt: Eine Figur geht auf dem Gitter $`\mathbb{Z} \times \mathbb{Z}`, und jeder Zug ist
sicher. Ein Zug ist eine Abbildung `north : Pos → m Pos` in eine *Monade* `m`, und ein Weg ist ein
Programm: `pure (0, 0) >>= north >>= east` beginnt in $`(0, 0)`, geht nach Norden, dann nach Osten.
Zuerst ist die Monade `Id`, die Monade der sicheren Ergebnisse: Der Weg endet in einem Punkt. Dann ist
es `Set`: Ein Zug kann in mehrere Richtungen gehen, und der Weg endet in der Menge der Punkte, die er
erreichen kann. In den Welten danach ist es die Monade der Verteilungen, und ein Zug geht mit einer
Wahrscheinlichkeit in jede Richtung.
:::

::::walk (target := "0,1") (moves := "north, east, south, west") (proof := ": (pure (0, 0) >>= north : Id Pos) = pure (0, 1)") (new := "rw, rfl, pure_bind, north, east, south, west") (play := "north")
:::en
*One step.* Bring the figure to the flag. Below the board is the walk so far, as Lean writes it, and
what Lean makes of it.
:::

:::de
*Ein Schritt.* Bring die Figur zur Fahne. Unter dem Spielfeld steht der Weg bisher, wie Lean ihn
schreibt, und was Lean daraus macht.
:::

:::proofen
*Now the proof.* What the board showed, now in Lean. Below is the *goal*, what is to be shown. In
`Id`, `pure a` is just the point `a`, and `pure a >>= f` is `f` applied to `a`: that is the rule
`pure_bind : pure a >>= f = f a`. The tactic `rw [pure_bind]` *rewrites* the goal with it: it replaces
the left side of the rule by its right side. Then `rw [north]` unfolds the move,
`north (x, y) = pure (x, y + 1)`. Last, `rfl` computes `0 + 1 = 1` and closes the goal. Type one
line after the other (or tap a rule in the inventory) and press *Run*.
:::

:::proofde
*Jetzt der Beweis.* Was das Spielfeld gezeigt hat, jetzt in Lean. Unten steht das *Ziel*, also das,
was zu zeigen ist. In `Id` ist `pure a` einfach der Punkt `a`, und `pure a >>= f` ist `f`, angewandt
auf `a`: Das ist die Regel `pure_bind : pure a >>= f = f a`. Die Taktik `rw [pure_bind]` *schreibt*
das Ziel damit *um*: Sie ersetzt die linke Seite der Regel durch ihre rechte. Dann wickelt
`rw [north]` den Zug aus, `north (x, y) = pure (x, y + 1)`. Zuletzt rechnet `rfl` `0 + 1 = 1` aus und
schließt das Ziel. Tippe eine Zeile nach der anderen ein (oder tippe eine Regel im Inventar an) und
drücke *Ausführen*.
:::
:::solution
```
rw [pure_bind]
rw [north]
rfl
```
:::
::::

::::walk (target := "1,1") (moves := "north, east, south, west") (proof := ": (pure (0, 0) >>= north >>= east : Id Pos) = pure (1, 1)") (new := "simp only") (play := "north, east")
:::en
*Around the corner.* Two steps.
:::

:::de
*Um die Ecke.* Zwei Schritte.
:::

:::proofen
With `rw` this needs four rules, one after the other. `simp only [pure_bind, north, east]` rewrites
with all of them, everywhere and as often as it can. Then `rfl`.
:::

:::proofde
Mit `rw` braucht das vier Regeln, eine nach der anderen. `simp only [pure_bind, north, east]` schreibt
mit allen um, überall und so oft es geht. Dann `rfl`.
:::
:::solution
```
simp only [pure_bind, north, east]
rfl
```
:::
::::

::::walk (target := "1,1") (moves := "north, east, south, west") (walls := "0,1") (proof := "(x y : ℤ) : (pure (x, y) >>= east >>= north : Id Pos) = pure (x, y) >>= north >>= east") (play := "east, north")
:::en
*The other way.* A wall blocks the way north. Go east first.
:::

:::de
*Der andere Weg.* Eine Wand versperrt den Weg nach Norden. Geh zuerst nach Osten.
:::

:::proofen
East then north ends where north then east ends, from every start $`(x, y)`. `simp only` rewrites
both sides to `pure (x + 1, y + 1)` and closes the goal itself; there is nothing to compute.
:::

:::proofde
Osten, dann Norden endet dort, wo Norden, dann Osten endet, von jedem Anfang $`(x, y)` aus.
`simp only` schreibt beide Seiten zu `pure (x + 1, y + 1)` um und schließt das Ziel selbst; es gibt
nichts auszurechnen.
:::
:::solution
```
simp only [pure_bind, north, east]
```
:::
::::

::::walk (monad := "Set") (target := "2,0 0,0 1,1 1,-1") (moves := "step, north, east, south, west") (proof := ": (pure (0, 0) >>= east >>= step : Set Pos) = {(2, 0), (0, 0), (1, 1), (1, -1)}") (new := "step") (play := "east, step")
:::en
*Everywhere at once.* Now a move may go several ways: `step` goes to all four neighbours. The figure
is now a set of points, all those it can reach. This is the monad `Set`: `pure a` is the set
$`\{a\}`, and `s >>= f` is the union of the sets `f a` over all `a ∈ s`. `north`, `east`, … are the
moves from before, now as sure moves in `Set`. Reach exactly the points marked.
:::

:::de
*Überall zugleich.* Jetzt kann ein Zug in mehrere Richtungen gehen: `step` geht zu allen vier
Nachbarn. Die Figur ist jetzt eine Menge von Punkten, alle, die sie erreichen kann. Das ist die
Monade `Set`: `pure a` ist die Menge $`\{a\}`, und `s >>= f` ist die Vereinigung der Mengen `f a` über
alle `a ∈ s`. `north`, `east`, … sind die Züge von vorher, jetzt als sichere Züge in `Set`. Erreiche
genau die markierten Punkte.
:::

:::proofen
The same rules as in `Id`: `pure_bind` holds in every monad. New is
`step (x, y) = {(x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1)}`.

*Tip.* `simp only [pure_bind, east, step]`, then `rfl`.
:::

:::proofde
Dieselben Regeln wie in `Id`: `pure_bind` gilt in jeder Monade. Neu ist
`step (x, y) = {(x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1)}`.

*Tipp.* `simp only [pure_bind, east, step]`, dann `rfl`.
:::
:::solution
```
simp only [pure_bind, east, step]
rfl
```
:::
::::

::::walk (monad := "Set") (target := "walk 2") (moves := "step, north, east, south, west") (proof := ": (0, 0) ∈ (pure (0, 0) >>= step >>= step : Set Pos)") (new := "apply, constructor, exists, step_east, step_west, mem_bind") (play := "step, step")
:::en
*Back home.* Two steps in any direction. The start is among the points again.
:::

:::de
*Wieder zu Hause.* Zwei Schritte in alle Richtungen. Der Anfang ist wieder unter den Punkten.
:::

:::proofen
A point is in `s >>= f` when there is a way to it: a point `a ∈ s` from which `f` reaches it. That is
`mem_bind : b ∈ s >>= f ↔ ∃ a ∈ s, b ∈ f a`. After `rw [mem_bind]`, the tactic `exists (1, 0)` names
such a point. Two facts remain, joined by `∧`: $`(1, 0)` is one step from the start, and $`(0, 0)`
one step from $`(1, 0)`. The tactic `constructor` splits them into two goals, one after the other.
The rules `step_east : (x + 1, y) ∈ step (x, y)` and `step_west : (x - 1, y) ∈ step (x, y)` say that
east and west are among the ways of `step`; the tactic `apply step_east` closes a goal of this form
(Lean computes `0 + 1 = 1` by itself).

*Tip.* `rw [mem_bind]`, `exists (1, 0)`, `constructor`, `rw [pure_bind]`, `apply step_east`,
`apply step_west`.
:::

:::proofde
Ein Punkt liegt in `s >>= f`, wenn es einen Weg zu ihm gibt: einen Punkt `a ∈ s`, von dem aus `f` ihn
erreicht. Das ist `mem_bind : b ∈ s >>= f ↔ ∃ a ∈ s, b ∈ f a`. Nach `rw [mem_bind]` nennt die Taktik
`exists (1, 0)` so einen Punkt. Zwei Tatsachen bleiben: $`(1, 0)` ist einen Schritt vom Anfang
entfernt, und $`(0, 0)` einen Schritt von $`(1, 0)`, verbunden durch `∧`. Die
Taktik `constructor` teilt sie in zwei Ziele, eines nach dem anderen. Die Regeln
`step_east : (x + 1, y) ∈ step (x, y)` und `step_west : (x - 1, y) ∈ step (x, y)` sagen, dass Osten
und Westen unter den Wegen von `step` sind; die Taktik `apply step_east` schließt ein Ziel dieser
Form (`0 + 1 = 1` rechnet Lean selbst aus).

*Tipp.* `rw [mem_bind]`, `exists (1, 0)`, `constructor`, `rw [pure_bind]`, `apply step_east`,
`apply step_west`.
:::
:::solution
```
rw [mem_bind]
exists (1, 0)
constructor
rw [pure_bind]
apply step_east
apply step_west
```
:::
::::

::::walk (monad := "Set") (target := "walk 3") (moves := "step, north, east, south, west") (colours := "yes") (proof := "(μ : Set Pos) : odd <$> (μ >>= step) = not <$> (odd <$> μ)") (lemma := "odd_bind_step") (new := "map_map, map_bind, map_eq_pure_bind, odd_step") (play := "step, step, step")
:::en
*Colours.* The grid is now a chessboard: $`(x, y)` is dark when $`x + y` is odd. Walk three steps,
and watch the colours of the points after each step.
:::

:::de
*Farben.* Das Gitter ist jetzt ein Schachbrett: $`(x, y)` ist dunkel, wenn $`x + y` ungerade ist. Geh
drei Schritte und achte nach jedem Schritt auf die Farben der Punkte.
:::

:::proofen
`odd p` says whether `p` lies on a dark field, and `odd <$> s` is the set of the colours of the points
of `s`. A step changes the colour, whichever way it goes:
`odd_step : odd <$> step p = pure (!odd p)`. So after a step the colours are those from before,
flipped by `not`, as the coin in *One Coin*. New rules: `map_bind : f <$> (s >>= g) = s >>= fun a => f <$> g a`,
`map_map : g <$> (f <$> s) = (fun x => g (f x)) <$> s` and
`map_eq_pure_bind : f <$> s = s >>= fun x => pure (f x)`. The lemma is called `odd_bind_step`.

*Tip.* `rw [map_bind]`, then `simp only [odd_step]` (inside `fun a => …` `rw` cannot rewrite), then
`rw [map_map, map_eq_pure_bind]`.
:::

:::proofde
`odd p` sagt, ob `p` auf einem dunklen Feld liegt, und `odd <$> s` ist die Menge der Farben der Punkte
von `s`. Ein Schritt wechselt die Farbe, in welche Richtung er auch geht:
`odd_step : odd <$> step p = pure (!odd p)`. Nach einem Schritt sind die Farben also die von vorher,
mit `not` umgedreht, wie die Münze in *Eine Münze*. Neue Regeln:
`map_bind : f <$> (s >>= g) = s >>= fun a => f <$> g a`,
`map_map : g <$> (f <$> s) = (fun x => g (f x)) <$> s` und
`map_eq_pure_bind : f <$> s = s >>= fun x => pure (f x)`. Das Lemma heißt `odd_bind_step`.

*Tipp.* `rw [map_bind]`, dann `simp only [odd_step]` (in `fun a => …` kann `rw` nicht umschreiben),
dann `rw [map_map, map_eq_pure_bind]`.
:::
:::solution
```
rw [map_bind]
simp only [odd_step]
rw [map_map, map_eq_pure_bind]
```
:::
::::

::::walk (monad := "Set") (target := "walk 4") (moves := "step, north, east, south, west") (colours := "yes") (proof := "(n : ℕ) : odd <$> walk n = pure n.bodd") (lemma := "odd_walk") (new := "induction', map_pure, walk_zero, walk_succ, Nat.bodd_succ") (play := "step, step, step, step")
:::en
*Boss: one colour.* Four steps. All points have the same colour, and it is the colour of $`4`: light,
since $`4` is even.
:::

:::de
*Endgegner: eine Farbe.* Vier Schritte. Alle Punkte haben dieselbe Farbe, und es ist die Farbe von
$`4`: hell, weil $`4` gerade ist.
:::

:::proofen
*Boss.* `walk n` is the set after $`n` steps: `walk_zero : walk 0 = pure (0, 0)` and
`walk_succ : walk (n + 1) = walk n >>= step`. `n.bodd` says whether $`n` is odd, and
`Nat.bodd_succ : (n + 1).bodd = !n.bodd`. The colours after $`n` steps are only the colour of
$`n`, for every $`n`: that needs *induction*. `induction' n with n ih` leaves two goals, one after
the other: the case $`0`, and the case $`n + 1`, with the hypothesis `ih` for $`n`. New also:
`map_pure : f <$> pure a = pure (f a)`. The lemma is called `odd_walk`.

*Tip.* Case $`0`: `rw [walk_zero, map_pure]`, then `rfl`. Case $`n + 1`:
`rw [walk_succ, odd_bind_step, ih, map_pure, Nat.bodd_succ]`.
:::

:::proofde
*Endgegner.* `walk n` ist die Menge nach $`n` Schritten: `walk_zero : walk 0 = pure (0, 0)` und
`walk_succ : walk (n + 1) = walk n >>= step`. `n.bodd` sagt, ob $`n` ungerade ist, und
`Nat.bodd_succ : (n + 1).bodd = !n.bodd`. Die Farben nach $`n` Schritten sind nur die Farbe von
$`n`, für jedes $`n`: Dafür braucht es *Induktion*. `induction' n with n ih` lässt zwei Ziele, eines
nach dem anderen: den Fall $`0`, und den Fall $`n + 1`, mit der Annahme `ih` für $`n`. Neu ist auch
`map_pure : f <$> pure a = pure (f a)`. Das Lemma heißt `odd_walk`.

*Tipp.* Fall $`0`: `rw [walk_zero, map_pure]`, dann `rfl`. Fall $`n + 1`:
`rw [walk_succ, odd_bind_step, ih, map_pure, Nat.bodd_succ]`.
:::
:::solution
```
induction' n with n ih
rw [walk_zero, map_pure]
rfl
rw [walk_succ, odd_bind_step, ih, map_pure, Nat.bodd_succ]
```
:::
::::

::::walk (monad := "Set") (target := "walk 5") (moves := "step, north, east, south, west") (colours := "yes") (proof := ": (0, 0) ∉ walk 5") (new := "cases, intro, have, mem_map") (play := "step, step, step, step, step")
:::en
*Never home.* Five steps. The start is not among the points: after an odd number of steps, the
figure is never at home.
:::

:::de
*Nie zu Hause.* Fünf Schritte. Der Anfang ist nicht unter den Punkten: Nach einer ungeraden Zahl von
Schritten ist die Figur nie zu Hause.
:::

:::proofen
`a ∉ s` means: from `a ∈ s` follows a contradiction. `intro h` assumes `h : (0, 0) ∈ walk 5`.
`mem_map : a ∈ s → f a ∈ f <$> s`, so `have h2 := mem_map odd h` gives
`h2 : odd (0, 0) ∈ odd <$> walk 5`. Your lemma `odd_walk` turns this into
`odd (0, 0) ∈ pure (Nat.bodd 5)` (`rw [odd_walk] at h2` rewrites `h2` instead of the goal). That
says `false = true`, and `cases h2` sees that this cannot be.

With probabilities, `odd_bind_step` and `odd_walk` have the same proofs: they use only the monad
laws and `odd_step`, which holds for the random walk as well. So after an odd number of steps, the
random walk is at home with probability $`0`.
:::

:::proofde
`a ∉ s` heißt: Aus `a ∈ s` folgt ein Widerspruch. `intro h` nimmt `h : (0, 0) ∈ walk 5` an.
`mem_map : a ∈ s → f a ∈ f <$> s`, also gibt `have h2 := mem_map odd h` die Aussage
`h2 : odd (0, 0) ∈ odd <$> walk 5`. Dein Lemma `odd_walk` macht daraus
`odd (0, 0) ∈ pure (Nat.bodd 5)` (`rw [odd_walk] at h2` schreibt `h2` um statt des Ziels). Das sagt
`false = true`, und `cases h2` sieht, dass das nicht sein kann.

Mit Wahrscheinlichkeiten haben `odd_bind_step` und `odd_walk` dieselben Beweise: Sie benutzen nur die
Monadengesetze und `odd_step`, das auch für die Irrfahrt gilt. Nach einer ungeraden Zahl von
Schritten ist die Irrfahrt also mit Wahrscheinlichkeit $`0` zu Hause.
:::
:::solution
```
intro h
have h2 := mem_map odd h
rw [odd_walk] at h2
cases h2
```
:::
::::
