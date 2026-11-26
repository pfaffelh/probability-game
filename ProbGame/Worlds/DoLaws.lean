import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Laws of `do`" =>

%%%
htmlSplit := .never
%%%

:::en
A gate before a coin, a gate after two coins, a coin that is not used: the circuits grow. Computing
every mass, as in *Two Coins*, grows faster: three coins have eight rows. This world goes another way:
laws that say how a circuit may be rebuilt without changing its distribution. On the board nothing is
new: coins at the inputs, and the distribution of the output is the target.
:::

:::proofen
A gate applied to a coin is a move, `(coin p).map not`; a throw is a draw, `let x ← coin p`. Three laws
say how moves and draws go together: a move is a `do` block; a move before a draw goes into what
follows; a move after a `do` block goes into it. You prove each of them on `Bool`, once, by computing
masses. Then it is yours for every type, and a `do` block is rewritten, not computed.
:::

:::de
Ein Baustein vor einer Münze, ein Baustein nach zwei Münzen, eine Münze, die nicht benutzt wird: Die
Schaltungen wachsen. Jede Masse auszurechnen, wie in *Zwei Münzen*, wächst schneller: Drei Münzen haben
acht Zeilen. Diese Welt geht einen anderen Weg: Gesetze, die sagen, wie man eine Schaltung umbauen darf,
ohne ihre Verteilung zu ändern. Auf dem Spielfeld ist nichts neu: Münzen an den Eingängen, und die
Verteilung des Ausgangs ist das Ziel.
:::

:::proofde
Ein Baustein, auf eine Münze angewandt, ist ein Zug, `(coin p).map not`; ein Wurf ist eine Ziehung,
`let x ← coin p`. Drei Gesetze sagen, wie Züge und Ziehungen zusammengehen: Ein Zug ist ein `do`-Block;
ein Zug vor einer Ziehung wandert in das, was folgt; ein Zug nach einem `do`-Block wandert in ihn
hinein. Du beweist jedes davon auf `Bool`, einmal, indem du Massen ausrechnest. Dann gehört es dir für
jeden Typ, und ein `do`-Block wird umgeschrieben, nicht ausgerechnet.
:::
:::::circuit (height := "440") (inputs := "x") (gates := "not") (coins := "p") (target := "bool true:p false:1-p") (context := "Lean/Rules.lean") (proof := "(p : I) : ((coin p).map not).map not = coin p") (shape := "!(!x)") (start := "a=not; x>a.0") (play := "b=not; a>b.0; b>out") (uses := "map_map, Bool.not_not, map_id")
:::hint (anchor := "none")
:::

:::en
*Flipped twice.* One `not` is given; the target is the coin itself.
:::

:::de
*Zweimal umgedreht.* Ein `nicht` ist gegeben; das Ziel ist die Münze selbst.
:::

:::proofen
Two moves, one after the other. No mass is computed: your boss lemma `map_map` from *Maps* makes
them one move, and that move you know from *Turned over twice, in one move*.
:::

:::proofde
Zwei Züge nacheinander. Keine Masse wird ausgerechnet: Dein Endgegner-Lemma `map_map` aus
*Abbildungen* macht aus ihnen einen Zug, und diesen Zug kennst du aus *Zweimal umgedreht, in einem Zug*.
:::
:::solution
```
rw [map_map]
simp_rw [Bool.not_not]
rw [map_id]
```
:::
:::::

:::::leanonly (proof := "(μ : DiscreteMeasure Bool) (f : Bool → Bool) : μ.map f = (do let x ← μ; ⟦pure (f x) ‖ pure (f x), pure x, μ.map f⟧)") (lemma := "map_eq_pure_bind") (uses := "map_apply, bind_apply, Fintype.sum_bool, pure_apply")
::::hint (anchor := "statement")
:::en
A move `μ.map f` is a `do` block: draw `x` from `μ`, then `f x` for sure.
:::

:::de
Ein Zug `μ.map f` ist ein `do`-Block: `x` aus `μ` ziehen, dann sicher `f x`.
:::
::::

:::en
*A move is a `do` block.* A move `μ.map f` draws `x` from `μ` and computes `f x`, for sure.
:::

:::de
*Ein Zug ist ein `do`-Block.* Ein Zug `μ.map f` zieht `x` aus `μ` und rechnet `f x` aus, sicher.
:::

:::proofen
Compare the masses at every `b`, with the definitions `map_apply` and `bind_apply`. What `f` does is
unknown, and so is `b`: eight cases, and in each `simp` computes. You prove it on `Bool`; it holds
for every type, and it is unlocked as `map_eq_pure_bind` in this general form.
:::

:::proofde
Vergleiche die Massen bei jedem `b`, mit den Definitionen `map_apply` und `bind_apply`. Was `f` tut,
ist unbekannt, und `b` auch: acht Fälle, und in jedem rechnet `simp`. Du beweist es auf `Bool`; es
gilt für jeden Typ und wird in dieser allgemeinen Form als `map_eq_pure_bind` freigeschaltet.
:::
:::solution
```
ext b
rw [map_apply, bind_apply]
simp_rw [Fintype.sum_bool, pure_apply]
cases f true <;> cases f false <;> cases b <;> simp
```
:::
:::::

:::::circuit (height := "440") (inputs := "x") (gates := "not, and, or") (coins := "p") (target := "bool true:1-p false:p") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; pure (!x)) = coin (σ p)") (play := "a=not; x>a.0; a>out") (uses := "map_eq_pure_bind, coin_not")
:::en
*A gate is a draw.* One coin, one `not`.
:::

:::de
*Ein Baustein ist eine Ziehung.* Eine Münze, ein `not`.
:::

:::proofen
Your new law `map_eq_pure_bind`, read the other way round: a `do` block that only applies a gate is a move.
:::

:::proofde
Dein neues Gesetz `map_eq_pure_bind`, andersherum gelesen: Ein `do`-Block, der nur einen Baustein anwendet, ist ein Zug.
:::
:::solution
```
rw [← map_eq_pure_bind, coin_not]
```
:::
:::::

:::::leanonly (proof := "(μ : DiscreteMeasure Bool) (f : Bool → Bool) (g : Bool → DiscreteMeasure Bool) : (do let x ← μ.map f; g x) = (do let x ← μ; ⟦g (f x) ‖ g (f x), g x, (g x).map f⟧)") (lemma := "bind_map_left") (uses := "bind_apply, Fintype.sum_bool, map_apply")
::::hint (anchor := "gap")
:::en
First move with `f`, then go on with `g`: in one draw, with what does `g` go on?
:::

:::de
Erst mit `f` bewegen, dann mit `g` weitermachen: In einem Zug, womit macht `g` weiter?
:::
::::

:::en
*A move before a draw.* Drawing from a moved distribution is drawing from the distribution and moving
the result.
:::

:::de
*Ein Zug vor dem Ziehen.* Aus einer bewegten Verteilung ziehen heißt, aus der Verteilung ziehen und das
Ergebnis bewegen.
:::

:::proofen
As in the level before: the masses at every `b`, all sums written out, also those inside
`map_apply`, and the four possible `f`. The simplifier computes, `ring` (from *Two Coins*) does the
rest. You prove it on `Bool`; it holds for every type, and it is unlocked as `bind_map_left` in this
general form.
:::

:::proofde
Wie im Level davor: die Massen bei jedem `b`, alle Summen ausgeschrieben, auch die in `map_apply`,
und die vier möglichen `f`. Der Simplifier rechnet, `ring` (aus *Zwei Münzen*) erledigt den Rest. Du
beweist es auf `Bool`; es gilt für jeden Typ und wird in dieser allgemeinen Form als `bind_map_left`
freigeschaltet.
:::
:::solution
```
ext b
rw [bind_apply, bind_apply]
simp_rw [Fintype.sum_bool, map_apply, Fintype.sum_bool]
cases f true <;> cases f false <;> simp <;> ring
```
:::
:::::

::::circuit (height := "540") (inputs := "x y") (gates := "and, or, not") (coins := "p p") (target := "bool true:p(1-p) false:1-p(1-p)") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure (x && !y)) = coin (p * σ p)") (play := "a=not; b=and; y>a.0; x>b.0; a>b.1; b>out") (uses := "coin_and, coin_not, bind_map_left, map_bind")
:::en
*First `true`, then `false`.*
:::

:::de
*Erst `true`, dann `false`.*
:::

:::proofen
`rw` does not reach under bound names; `simp_rw` (from *Maps*) does.
:::

:::proofde
`rw` reicht nicht unter gebundene Namen; `simp_rw` (aus *Abbildungen*) schon.
:::
:::solution
```
rw [← coin_and]
rw [← coin_not]
simp_rw [bind_map_left]
```
:::
::::

:::::leanonly (proof := "(μ : DiscreteMeasure Bool) (g : Bool → DiscreteMeasure Bool) (f : Bool → Bool) : (do let x ← μ; g x).map f = (do let x ← μ; ⟦(g x).map f ‖ (g x).map f, g (f x), g x⟧)") (lemma := "map_bind") (uses := "map_apply, bind_apply, Fintype.sum_bool")
::::hint (anchor := "gap")
:::en
A move after the whole draw: where can it go inside?
:::

:::de
Ein Zug nach dem ganzen Ziehen: Wohin kann er hinein?
:::
::::

:::en
*A move after a draw.* A move at the end can go into the `do` block.
:::

:::de
*Ein Zug nach dem Ziehen.* Ein Zug am Ende kann in den `do`-Block hinein.
:::

:::proofen
As for `bind_map_left`, now with the two `b` as well. You prove it on `Bool`; it holds for every
type, and it is unlocked as `map_bind` in this general form.
:::

:::proofde
Wie bei `bind_map_left`, jetzt auch mit den zwei `b`. Du beweist es auf `Bool`; es gilt für jeden
Typ und wird in dieser allgemeinen Form als `map_bind` freigeschaltet.
:::
:::solution
```
ext b
rw [map_apply, bind_apply]
simp_rw [Fintype.sum_bool, bind_apply, map_apply, Fintype.sum_bool]
cases f true <;> cases f false <;> cases b <;> simp <;> ring
```
:::
:::::

:::::circuit (height := "480") (inputs := "x y") (gates := "and, or, not") (coins := "p p") (target := "bool true:1-p^2 false:p^2") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure (x && y)).map not = (do let x ← coin p; let y ← coin p; pure (!(x && y)))") (play := "a=and; b=not; x>a.0; y>a.1; a>b.0; b>out") (uses := "map_bind, map_pure, bind_map_left")
:::en
*The gate at the end.* Two coins, `and`, then `not`.
:::

:::de
*Der Baustein am Ende.* Zwei Münzen, `and`, dann `not`.
:::

:::proofen
Your new law `map_bind`, under both draws, and `map_pure` at the end.
:::

:::proofde
Dein neues Gesetz `map_bind`, unter beiden Ziehungen, und `map_pure` am Ende.
:::
:::solution
```
simp_rw [map_bind, map_pure]
```
:::
:::::

:::::leanonly (proof := "(p : I) (ν : DiscreteMeasure Bool) : (do let _ ← coin p; ν) = ⟦ν ‖ ν, coin p, pure true⟧") (lemma := "coin_unused") (new := "add_mul") (uses := "bind_apply, Fintype.sum_bool, add_mul")
::::hint (anchor := "gap")
:::en
The outcome of the coin is not used (`_`): what is left?
:::

:::de
Das Ergebnis der Münze wird nicht benutzt (`_`): Was bleibt?
:::
::::

:::en
*An unused coin.* A coin whose outcome is not used changes nothing.
:::

:::de
*Eine unbenutzte Münze.* Eine Münze, deren Ergebnis nicht benutzt wird, ändert nichts.
:::

:::proofen
At every `b`, both ways go on with the same `ν b`. `ring` cannot use that $`p` and $`1 - p` add up
to one; so take `ν b` out yourself, with the new rule `add_mul : (a + b) * c = a * c + b * c`,
backwards. It is unlocked as `coin_unused`.
:::

:::proofde
Bei jedem `b` machen beide Wege mit demselben `ν b` weiter. `ring` kann nicht benutzen, dass sich
$`p` und $`1 - p` zu eins addieren; zieh `ν b` also selbst heraus, mit der neuen Regel
`add_mul : (a + b) * c = a * c + b * c`, rückwärts. Es wird als `coin_unused` freigeschaltet.
:::
:::solution
```
ext b
rw [bind_apply, Fintype.sum_bool, ← add_mul]
simp
```
:::
:::::

:::::circuit (height := "440") (inputs := "x y") (gates := "and, or, not") (coins := "p p") (target := "bernoulli p") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let _ ← coin p; let y ← coin p; pure y) = coin p") (play := "y>out") (uses := "coin_unused, prob_unused")
:::en
*One coin too many.* Two coins, and one of them is not used.
:::

:::de
*Eine Münze zu viel.* Zwei Münzen, und eine davon wird nicht benutzt.
:::

:::proofen
Your new law `coin_unused`.
:::

:::proofde
Dein neues Gesetz `coin_unused`.
:::
:::solution
```
rw [coin_unused]
```
:::
:::::

::::circuit (height := "540") (inputs := "x") (gates := "and, or, not") (coins := "p") (target := "pure false") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; pure (x && !x)) = pure false") (play := "a=not; b=and; x>a.0; x>b.0; a>b.1; b>out") (uses := "coin_unused, prob_unused")
:::en
*Surely `false`, with a single coin.* A coin that goes into two functions is the same coin in both:
the results depend on each other.
:::

:::de
*Sicher `false`, mit einer einzigen Münze.* Eine Münze, die in zwei Funktionen geht, ist in beiden
dieselbe: Die Ergebnisse hängen voneinander ab.
:::

:::proofen
`x && !x` is never `true`: your lemma `Bool.and_not_self` from *Bool*, marked simp. Then the coin is
no longer used.
:::

:::proofde
`x && !x` ist nie `true`: dein Lemma `Bool.and_not_self` aus *Bool*, mit der Marke simp. Dann wird
die Münze nicht mehr benutzt.
:::
:::solution
```
simp
rw [coin_unused]
```
:::
::::

:::::leanonly (proof := "(p : I) : (do let x ← coin p; pure (x && x)) = (do let x ← coin p; pure ⟦x || x ‖ x || x, !x, x && !x⟧)") (new := "congr") (uses := "-")
::::hint (anchor := "gap")
:::en
Which result is the same as `x && x`, for every `x`?
:::

:::de
Welches Ergebnis ist dasselbe wie `x && x`, für jedes `x`?
:::
::::

:::en
*The same coin, two results.* Both sides throw the same coin and differ only in what they do with it.
:::

:::de
*Dieselbe Münze, zwei Ergebnisse.* Beide Seiten werfen dieselbe Münze und unterscheiden sich nur darin,
was sie damit tun.
:::

:::proofen
A new tactic: `congr` reduces the goal to the parts in which the two sides differ, here what comes
after the throw, as a function of `x`. For two functions, `ext x` (from *One Coin*) says: equal for
every `x`.
:::

:::proofde
Eine neue Taktik: `congr` führt das Ziel auf die Teile zurück, in denen sich die beiden Seiten
unterscheiden, hier das, was nach dem Wurf kommt, als Funktion von `x`. Für zwei Funktionen sagt
`ext x` (aus *Eine Münze*): gleich für jedes `x`.
:::
:::solution
```
congr
ext x
cases x <;> rfl
```
:::
:::::

::::circuit (height := "540") (inputs := "x y") (gates := "or, not") (coins := "p p") (target := "bool true:1-p^2 false:p^2") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure (!x || !y)) = (do let x ← coin p; let y ← coin p; pure (!(x && y)))") (play := "a=not; b=not; c=or; x>a.0; y>b.0; a>c.0; b>c.1; c>out") (uses := "-")
:::en
*Not both `true`*, without an `and`: only `or` and `not` are there.
:::

:::de
*Nicht beide `true`*, ohne ein `and`: Es gibt nur `or` und `not`.
:::

:::proofen
Both sides throw the same two coins and differ only in what they compute: as in the level before,
once for each coin.
:::

:::proofde
Beide Seiten werfen dieselben zwei Münzen und unterscheiden sich nur darin, was sie rechnen: wie im
Level davor, einmal für jede Münze.
:::
:::solution
```
congr
ext x
congr
ext y
cases x <;> cases y <;> rfl
```
:::
::::

::::circuit (height := "440") (inputs := "x y") (gates := "and, or, not") (coins := "p p") (target := "bool true:2p-p^2 false:(1-p)^2") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure (x || y)) = coin (σ (σ p * σ p))") (play := "a=or; x>a.0; y>a.1; a>out") (uses := "coin_not, coin_and, bind_map_left, map_bind, map_pure, or_eq")
:::en
*Boss: at least one `true`.* `false` only when both show `false`: $`(1 - p)^2`.
:::

:::de
*Endgegner: mindestens einmal `true`.* `false` nur, wenn beide `false` zeigen: $`(1 - p)^2`.
:::

:::solution
```
rw [← coin_not]
rw [← coin_and]
rw [← coin_not]
simp_rw [bind_map_left, map_bind, map_pure, or_eq]
```
:::
::::
