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
every mass, as in *Coins*, grows faster: three coins have eight rows. This world goes another way:
laws that say how a circuit may be rebuilt without changing its distribution. On the board nothing is
new: coins at the inputs, and the distribution of the output is the target.
:::

:::proofen
A gate applied to a coin is a move, `(coin p).map not`; a throw is a draw, `let x ← coin p`. Laws say
how moves and draws go together: a move is a `do` block (from *Coins*); a draw from a point mass is no draw; a `do`
block in a `do` block is one `do` block; a move before a draw goes into what follows; a move after a
`do` block goes into it. You prove each of them on `Bool`, once, by computing masses or from the laws
before. Then it is yours for every type, and a `do` block is rewritten, not computed.
:::

:::de
Ein Baustein vor einer Münze, ein Baustein nach zwei Münzen, eine Münze, die nicht benutzt wird: Die
Schaltungen wachsen. Jede Masse auszurechnen, wie in *Münzen*, wächst schneller: Drei Münzen haben
acht Zeilen. Diese Welt geht einen anderen Weg: Gesetze, die sagen, wie man eine Schaltung umbauen darf,
ohne ihre Verteilung zu ändern. Auf dem Spielfeld ist nichts neu: Münzen an den Eingängen, und die
Verteilung des Ausgangs ist das Ziel.
:::

:::proofde
Ein Baustein, auf eine Münze angewandt, ist ein Zug, `(coin p).map not`; ein Wurf ist eine Ziehung,
`let x ← coin p`. Gesetze sagen, wie Züge und Ziehungen zusammengehen: Ein Zug ist ein `do`-Block; aus
einer Punktmasse ziehen ist kein Ziehen; ein `do`-Block in einem `do`-Block ist ein `do`-Block; ein Zug
vor einer Ziehung wandert in das, was folgt; ein Zug nach einem `do`-Block wandert in ihn hinein. Du
beweist jedes davon auf `Bool`, einmal, indem du Massen ausrechnest oder es aus den Gesetzen davor
herleitest. Dann gehört es dir für jeden Typ, und ein `do`-Block wird umgeschrieben, nicht ausgerechnet.
:::

:::::circuit (height := "440") (inputs := "x") (gates := "not") (coins := "p") (target := "bool true:p false:1-p") (context := "Lean/Rules.lean") (proof := "(p : I) : ((coin p).map not).map not = coin p") (shape := "!(!x)") (start := "a=not; x>a.0") (play := "b=not; a>b.0; b>out") (uses := "map_map, Bool.not_not, map_id, rw, simp, simp_rw")
:::hint (anchor := "none")
:::

:::en
*Flipped twice.* One `not` is given; the target is the coin itself.
:::

:::de
*Zweimal umgedreht.* Ein `nicht` ist gegeben; das Ziel ist die Münze selbst.
:::

:::proofen
Two moves, one after the other. No mass is computed: your lemma `map_map` from *DiscreteMeasure* makes
them one move, and that move you know from *Turned over twice, in one move*.
:::

:::proofde
Zwei Züge nacheinander. Keine Masse wird ausgerechnet: Dein Lemma `map_map` aus
*DiscreteMeasure* macht aus ihnen einen Zug, und diesen Zug kennst du aus *Zweimal umgedreht, in einem Zug*.
:::
:::solution
```
rw [map_map]
simp_rw [Bool.not_not]
rw [map_id]
```
:::
:::solution
```
rw [map_map]
simp_rw [Bool.not_not, map_id]
```
:::
:::solution
```
rw [map_map]
simp
rw [map_id]
```
:::
:::::

::::leanonly (proof := "(b : Bool) (f : Bool → DiscreteMeasure Bool) : (do let x ← pure b; f x) = ⟦f b ‖ f b, f true, pure b⟧") (lemma := "pure_bind") (uses := "bind_apply, Fintype.sum_bool, pure_true, pure_false, Bool.cond_false, zero_mul, one_mul, zero_add, Bool.cond_true, add_zero, mul_one, mul_zero, <;>, cases, ext, rw, simp")
:::en
*A sure draw.* Drawing from the point mass `pure b` gives `b`, for sure: the draw can be left out.
:::

:::de
*Eine sichere Ziehung.* Aus der Punktmasse `pure b` ziehen gibt sicher `b`: Die Ziehung kann weg.
:::

:::proofen
The masses at every `c`: `bind_apply`, then the masses of `pure b` (`pure_true`, `pure_false`), and
the two cases for `b`. You prove it on `Bool`; it holds for every type, and it is unlocked as
`pure_bind` in this general form.
:::

:::proofde
Die Massen bei jedem `c`: `bind_apply`, dann die Massen von `pure b` (`pure_true`, `pure_false`), und
die zwei Fälle für `b`. Du beweist es auf `Bool`; es gilt für jeden Typ und wird in dieser
allgemeinen Form als `pure_bind` freigeschaltet.
:::
:::solution
```
ext c
rw [bind_apply, Fintype.sum_bool, pure_true, pure_false]
cases b <;> simp
```
:::
:::solution
```
ext c
rw [bind_apply, Fintype.sum_bool]
cases b
rw [pure_true, pure_false, Bool.cond_false, Bool.cond_false, zero_mul, one_mul, zero_add]
rw [pure_true, pure_false, Bool.cond_true, Bool.cond_true, one_mul, zero_mul, add_zero]
```
:::
:::solution
```
ext c
rw [bind_apply, Fintype.sum_bool]
cases b <;> simp
```
:::
:::solution
```
ext c
cases b <;> simp [bind_apply, Fintype.sum_bool]
```
:::
::::

::::leanonly (proof := "(μ : DiscreteMeasure Bool) (f g : Bool → DiscreteMeasure Bool) : (do let y ← (do let x ← μ; f x); g y) = (do let x ← μ; let y ← f x; ⟦g y ‖ g y, g x, f y⟧)") (lemma := "bind_assoc") (uses := "bind_apply, Fintype.sum_bool, ext, ring, simp, simp_rw")
:::en
*A `do` block in a `do` block.* A two-stage experiment and then one stage more: that is one
three-stage experiment.
:::

:::de
*Ein `do`-Block in einem `do`-Block.* Ein zweistufiges Experiment und danach noch eine Stufe: Das ist
ein dreistufiges Experiment.
:::

:::proofen
The masses at every `c`, with `bind_apply` everywhere (under the `do`: `simp_rw`). Then both sides are
sums of products, and `ring` sees that they agree. You prove it on `Bool`; it holds for every type,
and it is unlocked as `bind_assoc` in this general form.
:::

:::proofde
Die Massen bei jedem `c`, mit `bind_apply` überall (unter dem `do`: `simp_rw`). Dann sind beide Seiten
Summen von Produkten, und `ring` sieht, dass sie übereinstimmen. Du beweist es auf `Bool`; es gilt für
jeden Typ und wird in dieser allgemeinen Form als `bind_assoc` freigeschaltet.
:::
:::solution
```
ext c
simp_rw [bind_apply, Fintype.sum_bool]
ring
```
:::
:::solution
```
ext c
simp [bind_apply, Fintype.sum_bool]
ring
```
:::
::::

:::::leanonly (proof := "(μ : DiscreteMeasure Bool) (f : Bool → Bool) (g : Bool → DiscreteMeasure Bool) : (do let x ← μ.map f; g x) = (do let x ← μ; ⟦g (f x) ‖ g (f x), g x, (g x).map f⟧)") (lemma := "bind_map_left") (uses := "map_eq_pure_bind, bind_assoc, pure_bind, bind_apply, Fintype.sum_bool, map_bool, bind_pure, <;>, cases, ext, ring, rw, simp, simp_rw")
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
From your laws: the move is a `do` block (`map_eq_pure_bind`), a `do` block in a `do` block is one
(`bind_assoc`), and the sure draw goes (`pure_bind`, under the `do`: `simp_rw`). Or compute the masses
at every `b`, as for `map_eq_pure_bind`. It holds for every type, and it is unlocked as
`bind_map_left` in this general form.
:::

:::proofde
Aus deinen Gesetzen: Der Zug ist ein `do`-Block (`map_eq_pure_bind`), ein `do`-Block in einem
`do`-Block ist einer (`bind_assoc`), und die sichere Ziehung fällt weg (`pure_bind`, unter dem `do`:
`simp_rw`). Oder rechne die Massen bei jedem `b` aus, wie bei `map_eq_pure_bind`. Es gilt für jeden
Typ und wird in dieser allgemeinen Form als `bind_map_left` freigeschaltet.
:::
:::solution
```
rw [map_eq_pure_bind, bind_assoc]
simp_rw [pure_bind]
```
:::
:::solution
```
ext b
rw [bind_apply, bind_apply]
simp_rw [Fintype.sum_bool, map_bool]
cases f true <;> cases f false <;> simp <;> ring
```
:::
:::solution
```
simp_rw [map_eq_pure_bind, bind_assoc, pure_bind]
```
:::
:::solution
```
rw [map_eq_pure_bind, bind_assoc]
simp
```
:::
:::::

::::circuit (height := "540") (inputs := "x y") (gates := "and, or, not") (coins := "p p") (target := "bool true:p(1-p) false:1-p(1-p)") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure (x && !y)) = coin (p * σ p)") (play := "a=not; b=and; y>a.0; x>b.0; a>b.1; b>out") (uses := "coin_and, coin_not, bind_map_left, map_eq_pure_bind, bind_assoc, pure_bind, bool_ext, bind_true, mass_mul, eq_coin, map_bind, bind_pure, apply, rw, simp, simp_rw")
:::en
*First `true`, then `false`.*
:::

:::de
*Erst `true`, dann `false`.*
:::

:::proofen
`rw` does not reach under bound names; `simp_rw` (from *DiscreteMeasure*) does.
:::

:::proofde
`rw` reicht nicht unter gebundene Namen; `simp_rw` (aus *DiscreteMeasure*) schon.
:::
:::solution
```
rw [← coin_and]
rw [← coin_not]
simp_rw [bind_map_left]
```
:::
:::solution
```
rw [← coin_and, ← coin_not]
simp_rw [map_eq_pure_bind, bind_assoc, pure_bind]
```
:::
:::solution
```
apply bool_ext
rw [bind_true, bind_true, bind_true]
simp [mass_mul]
```
:::
:::solution
```
apply eq_coin
rw [bind_true, bind_true, bind_true]
simp [mass_mul]
```
:::
::::

:::::leanonly (proof := "(μ : DiscreteMeasure Bool) (g : Bool → DiscreteMeasure Bool) (f : Bool → Bool) : (do let x ← μ; g x).map f = (do let x ← μ; ⟦(g x).map f ‖ (g x).map f, g (f x), g x⟧)") (lemma := "map_bind") (uses := "map_eq_pure_bind, bind_assoc, map_bool, bind_apply, Fintype.sum_bool, <;>, cases, ext, ring, rw, simp, simp_rw")
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
As for `bind_map_left`: from your laws, or by computing the masses. It holds for every type, and it
is unlocked as `map_bind` in this general form.
:::

:::proofde
Wie bei `bind_map_left`: aus deinen Gesetzen oder durch Ausrechnen der Massen. Es gilt für jeden Typ
und wird in dieser allgemeinen Form als `map_bind` freigeschaltet.
:::
:::solution
```
rw [map_eq_pure_bind, bind_assoc]
simp_rw [← map_eq_pure_bind]
```
:::
:::solution
```
ext b
rw [map_bool, bind_apply]
simp_rw [Fintype.sum_bool, bind_apply, map_bool, Fintype.sum_bool]
cases f true <;> cases f false <;> cases b <;> simp <;> ring
```
:::
:::solution
```
simp_rw [map_eq_pure_bind, bind_assoc]
```
:::
:::::

:::::circuit (height := "480") (inputs := "x y") (gates := "and, or, not") (coins := "p p") (target := "bool true:1-p^2 false:p^2") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure (x && y)).map not = (do let x ← coin p; let y ← coin p; pure (!(x && y)))") (play := "a=and; b=not; x>a.0; y>a.1; a>b.0; b>out") (uses := "map_bind, map_pure, map_eq_pure_bind, bind_assoc, pure_bind, bind_map_left, bind_pure, rw, simp_rw")
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
:::solution
```
rw [map_eq_pure_bind]
simp_rw [bind_assoc, pure_bind]
```
:::
:::solution
```
simp_rw [map_eq_pure_bind, bind_assoc, pure_bind]
```
:::
:::solution
```
rw [map_bind]
simp_rw [map_bind, map_pure]
```
:::
:::::

:::::leanonly (proof := "(p : I) (ν : DiscreteMeasure Bool) : (do let _ ← coin p; ν) = ⟦ν ‖ ν, coin p, pure true⟧") (lemma := "coin_unused") (uses := "bind_apply, Fintype.sum_bool, add_mul, coin_total, one_mul, mass_total, coin_true, coin_false, mul_one, ext, rw, simp")
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
to one; so take `ν b` out yourself, with `add_mul : (a + b) * c = a * c + b * c`,
backwards. It is unlocked as `coin_unused`.
:::

:::proofde
Bei jedem `b` machen beide Wege mit demselben `ν b` weiter. `ring` kann nicht benutzen, dass sich
$`p` und $`1 - p` zu eins addieren; zieh `ν b` also selbst heraus, mit der Regel
`add_mul : (a + b) * c = a * c + b * c`, rückwärts. Es wird als `coin_unused` freigeschaltet.
:::
:::solution
```
ext b
rw [bind_apply, Fintype.sum_bool, ← add_mul]
simp
```
:::
:::solution
```
ext b
rw [bind_apply, Fintype.sum_bool, ← add_mul, coin_total, one_mul]
```
:::
:::solution
```
ext b
rw [bind_apply, Fintype.sum_bool]
simp [← add_mul]
```
:::
:::solution
```
ext b
rw [bind_apply, Fintype.sum_bool, ← add_mul, mass_total, one_mul]
```
:::
:::::

:::::circuit (height := "440") (inputs := "x y") (gates := "and, or, not") (coins := "p p") (target := "bernoulli p") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let _ ← coin p; let y ← coin p; pure y) = coin p") (play := "y>out") (uses := "coin_unused, bool_ext, bind_true, add_mul, apply, exact, rw, simp, simp_rw")
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
:::solution
```
simp_rw [coin_unused]
```
:::
:::solution
```
apply bool_ext
rw [bind_true]
simp [← add_mul]
```
:::
:::solution
```
exact coin_unused p (coin p)
```
:::
:::::

::::circuit (height := "540") (inputs := "x") (gates := "and, or, not") (coins := "p") (target := "pure false") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; pure (x && !x)) = pure false") (play := "a=not; b=and; x>a.0; x>b.0; a>b.1; b>out") (uses := "coin_unused, Bool.and_not_self, bool_ext, bind_true, Bool.or_not_self, apply, rw, simp, simp_rw")
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
:::solution
```
simp_rw [Bool.and_not_self, coin_unused]
```
:::
:::solution
```
simp [coin_unused]
```
:::
:::solution
```
apply bool_ext
rw [bind_true]
simp
```
:::
::::

:::::leanonly (proof := "(p : I) : (do let x ← coin p; pure (x && x)) = (do let x ← coin p; pure ⟦x || x ‖ x || x, !x, x && !x⟧)") (new := "congr") (uses := "Bool.false_and, Bool.false_or, Bool.true_and, Bool.true_or, <;>, cases, congr, ext, rfl, rw, simp")
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
after the throw, as a function of `x`. For two functions, `ext x` (from *DiscreteMeasure*) says: equal for
every `x`.
:::

:::proofde
Eine neue Taktik: `congr` führt das Ziel auf die Teile zurück, in denen sich die beiden Seiten
unterscheiden, hier das, was nach dem Wurf kommt, als Funktion von `x`. Für zwei Funktionen sagt
`ext x` (aus *DiscreteMeasure*): gleich für jedes `x`.
:::
:::solution
```
congr
ext x
cases x <;> rfl
```
:::
:::solution
```
congr
ext x
cases x <;> simp
```
:::
:::solution
```
congr
ext x
cases x
rw [Bool.false_and, Bool.false_or]
rw [Bool.true_and, Bool.true_or]
```
:::
:::::

::::circuit (height := "540") (inputs := "x y") (gates := "or, not") (coins := "p p") (target := "bool true:1-p^2 false:p^2") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure (!x || !y)) = (do let x ← coin p; let y ← coin p; pure (!(x && y)))") (play := "a=not; b=not; c=or; x>a.0; y>b.0; a>c.0; b>c.1; c>out") (uses := "or_eq, Bool.not_not, Bool.not_and, bool_ext, bind_true, <;>, apply, cases, congr, ext, rfl, rw, simp, simp_rw")
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
:::solution
```
simp_rw [or_eq, Bool.not_not]
```
:::
:::solution
```
simp_rw [Bool.not_and]
```
:::
:::solution
```
apply bool_ext
rw [bind_true, bind_true, bind_true, bind_true, bind_true, bind_true]
simp
```
:::
::::

::::leanonly (proof := "(a : ℝ≥0∞) (p : I) (h : a + ↑p = 1) : a = ↑(σ p)") (lemma := "eq_symm_of_add") (uses := "coin_false, mass_not, Bool.not_false, coin_true, add_comm, ENNReal.add_sub_cancel_left, mass_ne_top, coin_total, Bool.not_true, add_assoc, rw")
:::en
*What is left to one.* If `a` and `p` add up to `1`, then `a` is the mass `σ p`, that is $`1 - p`.
:::

:::de
*Was zu eins fehlt.* Ergeben `a` und `p` zusammen `1`, dann ist `a` die Masse `σ p`, also $`1 - p`.
:::

:::proofen
`σ p` is the mass of `coin p` at `false`, and `mass_not` (from *DiscreteMeasure*) writes it as `1 - …`. Then
`h`, and take away what was added: `ENNReal.add_sub_cancel_left`. Your result becomes the lemma
`eq_symm_of_add`.
:::

:::proofde
`σ p` ist die Masse von `coin p` bei `false`, und `mass_not` (aus *DiscreteMeasure*) schreibt sie als
`1 - …`. Dann `h`, und nimm weg, was dazukam: `ENNReal.add_sub_cancel_left`. Dein Ergebnis wird das
Lemma `eq_symm_of_add`.
:::
:::solution
```
rw [← coin_false, mass_not (coin p) false, Bool.not_false]
rw [← h, ← coin_true]
rw [add_comm, ENNReal.add_sub_cancel_left mass_ne_top]
```
:::
::::

::::circuit (height := "440") (inputs := "x y") (gates := "and, or, not") (coins := "p p") (target := "bool true:2p-p^2 false:(1-p)^2") (context := "Lean/Rules.lean") (proof := "(p : I) : (do let x ← coin p; let y ← coin p; pure (x || y)) = coin (σ (σ p * σ p))") (play := "a=or; x>a.0; y>a.1; a>out") (uses := "coin_not, coin_and, bind_map_left, map_bind, map_pure, or_eq, bool_ext, bind_true, eq_symm_of_add, mass_mul, add_assoc, mul_add, Bool.not_and, Bool.not_not, map_eq_pure_bind, bind_assoc, pure_bind, add_comm, add_right_comm, bind_pure, apply, rw, simp, simp_rw")
:::en
*Boss: at least one `true`.* `false` only when both show `false`: $`(1 - p)^2`.
:::

:::de
*Endgegner: mindestens einmal `true`.* `false` nur, wenn beide `false` zeigen: $`(1 - p)^2`.
:::

:::proofen
Two ways. With the laws: build the right side from moves and draws (`coin_not`, `coin_and`) and
rewrite until both sides agree. Or compute the masses at `true`; at the end `eq_symm_of_add` turns
`↑(σ …)` into a sum that must give `1`.
:::

:::proofde
Zwei Wege. Mit den Gesetzen: Bau die rechte Seite aus Zügen und Ziehungen (`coin_not`, `coin_and`)
und schreib um, bis beide Seiten übereinstimmen. Oder rechne die Massen bei `true` aus; am Ende macht
`eq_symm_of_add` aus `↑(σ …)` eine Summe, die `1` ergeben muss.
:::

:::solution
```
rw [← coin_not]
rw [← coin_and]
rw [← coin_not]
simp_rw [bind_map_left, map_bind, map_pure, or_eq]
```
:::
:::solution
```
apply bool_ext
rw [bind_true, bind_true, bind_true]
simp
apply eq_symm_of_add
rw [mass_mul, add_assoc, ← mul_add]
simp
```
:::
:::solution
```
rw [← coin_not, ← coin_and, ← coin_not]
simp_rw [bind_map_left, map_bind, map_pure, Bool.not_and, Bool.not_not]
```
:::
:::solution
```
rw [← coin_not, ← coin_and, ← coin_not]
simp_rw [map_eq_pure_bind, bind_assoc, pure_bind, or_eq]
```
:::
::::
