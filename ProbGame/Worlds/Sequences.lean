import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Sequences" =>

%%%
htmlSplit := .never
%%%

:::en
Throwing $`n` coins one after the other gives a list of $`n` outcomes: `iidSequence n (coin p)`, a distribution on lists (independent, identically distributed). The mass of a list depends only on how many `true` and how many `false` it has. The boss: `binom p n` is the number of `true` in it. In Lean only.
:::

:::de
$`n` Münzen nacheinander werfen ergibt eine Liste von $`n` Ergebnissen: `iidSequence n (coin p)`, eine Verteilung auf Listen (unabhängig, identisch verteilt). Die Masse einer Liste hängt nur davon ab, wie viele `true` und wie viele `false` sie hat. Der Endgegner: `binom p n` ist die Anzahl der `true` darin. Nur in Lean.
:::

::::leanonly (proof := "(p : I) : iidSequence 1 (coin p) = (do let y ← coin p; pure [y])") (new := "seq_zero, seq_succ") (group := "chance.count") (uses := "seq_succ, seq_zero, pure_bind, bind_pure, rw, simp_rw")
:::en
*One throw, as a list.* `iidSequence n μ` draws $`n` times from `μ`, independently, and gives the list of the outcomes: a distribution on lists.
:::

:::de
*Ein Wurf, als Liste.* `iidSequence n μ` zieht $`n`-mal aus `μ`, unabhängig, und gibt die Liste der Ergebnisse: eine Verteilung auf Listen.
:::

:::proofen
The definition:

```
def iidSequence (n : ℕ) (μ : DiscreteMeasure α) : DiscreteMeasure (List α) :=
  sequence (List.replicate n μ)
```

(`sequence [μ₁, …, μₙ]` draws from each `μᵢ`, one after the other, independently, and gives the
list of the outcomes.)

For the game two rules: `seq_zero : iidSequence 0 μ = pure []` and `seq_succ : iidSequence (n + 1) μ = do let y ← μ; let l ← iidSequence n μ; pure (y :: l)` (`y :: l` is the list `l` with `y` in front; `[y]` is `y :: []`).
:::

:::proofde
Die Definition:

```
def iidSequence (n : ℕ) (μ : DiscreteMeasure α) : DiscreteMeasure (List α) :=
  sequence (List.replicate n μ)
```

(`sequence [μ₁, …, μₙ]` zieht aus jedem `μᵢ`, eins nach dem anderen, unabhängig, und gibt die
Liste der Ergebnisse.)

Fürs Spiel zwei Regeln: `seq_zero : iidSequence 0 μ = pure []` und `seq_succ : iidSequence (n + 1) μ = do let y ← μ; let l ← iidSequence n μ; pure (y :: l)` (`y :: l` ist die Liste `l` mit `y` vorne; `[y]` ist `y :: []`).
:::
:::solution
```
rw [seq_succ, seq_zero]
simp_rw [pure_bind]
```
:::
::::

::::leanonly (proof := "(p : I) : iidSequence 2 (coin p) [true, false] = ⟦↑p * ↑(σ p) ‖ ↑p * ↑p, ↑p + ↑(σ p), ↑p * ↑(σ p), ↑p⟧") (new := "seq_succ_apply, seq_zero_nil, mul_one") (group := "chance.count") (uses := "seq_succ_apply, seq_zero_nil, mul_one, coin_true, coin_false, one_mul, coin_total, rw")
:::en
*The mass of a sequence.* Independent: the mass of a list is the product of the masses of its entries. First `true`, then `false`.
:::

:::de
*Die Masse einer Folge.* Unabhängig: Die Masse einer Liste ist das Produkt der Massen ihrer Einträge. Erst `true`, dann `false`.
:::

:::proofen
`seq_succ_apply : iidSequence (n + 1) μ (a :: l) = μ a * iidSequence n μ l` and `seq_zero_nil : iidSequence 0 μ [] = 1` (`[true, false]` is `true :: false :: []`).
:::

:::proofde
`seq_succ_apply : iidSequence (n + 1) μ (a :: l) = μ a * iidSequence n μ l` und `seq_zero_nil : iidSequence 0 μ [] = 1` (`[true, false]` ist `true :: false :: []`).
:::
:::solution
```
rw [seq_succ_apply, seq_succ_apply, seq_zero_nil, mul_one, coin_true, coin_false]
```
:::
::::

::::leanonly (proof := "(l : List Bool) : (true :: l).count true = 1 + l.count true") (new := "count_true_cons, Bool.toNat_true") (group := "chance.count") (uses := "count_true_cons, Bool.toNat_true, rw")
:::en
*Counting true.* `l.count true` is the number of `true` in the list `l`. One in front counts as its number, `toNat`.
:::

:::de
*true zählen.* `l.count true` ist die Anzahl der `true` in der Liste `l`. Eins vorne zählt mit seiner Zahl, `toNat`.
:::

:::proofen
`count_true_cons : (y :: l).count true = y.toNat + l.count true`.
:::

:::proofde
`count_true_cons : (y :: l).count true = y.toNat + l.count true`.
:::
:::solution
```
rw [count_true_cons, Bool.toNat_true]
```
:::
::::

::::leanonly (proof := "(l : List Bool) : (true :: l).count false = l.count false") (new := "count_false_cons, Bool.toNat_false") (group := "chance.count") (uses := "count_false_cons, Bool.not_true, Bool.toNat_false, zero_add, Bool.not_false, add_zero, mul_zero, rw")
:::en
*Counting false.* A `true` in front is no `false` more.
:::

:::de
*false zählen.* Ein `true` vorne ist kein `false` mehr.
:::

:::proofen
`count_false_cons : (y :: l).count false = (!y).toNat + l.count false`: an entry counts as a `false` when its opposite is `true`. And `Bool.toNat_false : false.toNat = 0`.
:::

:::proofde
`count_false_cons : (y :: l).count false = (!y).toNat + l.count false`: Ein Eintrag zählt als `false`, wenn sein Gegenteil `true` ist. Und `Bool.toNat_false : false.toNat = 0`.
:::
:::solution
```
rw [count_false_cons, Bool.not_true, Bool.toNat_false, zero_add]
```
:::
::::

::::leanonly (proof := "(p : I) : iidSequence ([] : List Bool).length (coin p) [] = ↑p ^ ([] : List Bool).count true * ↑(σ p) ^ ([] : List Bool).count false") (new := "List.length_nil, List.count_nil") (group := "chance.count") (uses := "List.length_nil, seq_zero_nil, List.count_nil, ring, rw")
:::en
*The empty list.* A list `l` of throws has a mass: a factor $`p` for every `true` in it, a factor $`1 - p` for every `false`. First for the empty list: no throw, no factor.
:::

:::de
*Die leere Liste.* Eine Liste `l` von Würfen hat eine Masse: einen Faktor $`p` für jedes `true` darin, einen Faktor $`1 - p` für jedes `false`. Zuerst für die leere Liste: kein Wurf, kein Faktor.
:::

:::proofen
`List.length_nil : [].length = 0` and `List.count_nil : [].count a = 0`. A power with exponent $`0` is $`1`: `ring` knows.
:::

:::proofde
`List.length_nil : [].length = 0` und `List.count_nil : [].count a = 0`. Eine Potenz mit Exponent $`0` ist $`1`: Das weiß `ring`.
:::
:::solution
```
rw [List.length_nil, seq_zero_nil, List.count_nil, List.count_nil]
ring
```
:::
::::

::::leanonly (proof := "(p : I) (y : Bool) (l : List Bool) : coin p y * (↑p ^ l.count true * ↑(σ p) ^ l.count false) = ↑p ^ (y :: l).count true * ↑(σ p) ^ (y :: l).count false") (lemma := "mass_cons") (group := "chance.count") (uses := "count_true_cons, count_false_cons, coin_false, Bool.toNat_false, Bool.not_false, Bool.toNat_true, coin_true, Bool.not_true, coin_total, cases, ring, rw")
:::en
*One more in front.* One more throw `y` in front of the list `l`: its mass `coin p y` is one factor more, $`p` or $`1 - p`.
:::

:::de
*Einer mehr vorne.* Ein Wurf `y` mehr vor der Liste `l`: Seine Masse `coin p y` ist ein Faktor mehr, $`p` oder $`1 - p`.
:::

:::proofen
First both counts by their rules. Then `y` is `true` or `false`; the powers are for `ring`. Your
result becomes the lemma `mass_cons`.
:::

:::proofde
Zuerst beide Anzahlen mit ihren Regeln. Dann ist `y` `true` oder `false`; die Potenzen sind für
`ring`. Dein Ergebnis wird das Lemma `mass_cons`.
:::
:::solution
```
rw [count_true_cons, count_false_cons]
cases y
rw [coin_false, Bool.toNat_false, Bool.not_false, Bool.toNat_true]
ring
rw [coin_true, Bool.toNat_true, Bool.not_true, Bool.toNat_false]
ring
```
:::
::::

::::leanonly (proof := "(p : I) (l : List Bool) : iidSequence l.length (coin p) l = ↑p ^ l.count true * ↑(σ p) ^ l.count false") (lemma := "seq_mass") (new := "List.length_cons") (group := "chance.count") (uses := "List.length_nil, seq_zero_nil, List.count_nil, List.length_cons, seq_succ_apply, mass_cons, induction', ring, rw")
:::en
*The mass of a list.* Whatever the order: a list with $`k` times `true` and $`m` times `false` has the mass $`p^k (1 - p)^m`. (How many such lists there are: *Binomial*.)
:::

:::de
*Die Masse einer Liste.* In welcher Reihenfolge auch immer: Eine Liste mit $`k`-mal `true` und $`m`-mal `false` hat die Masse $`p^k (1 - p)^m`. (Wie viele solche Listen es gibt: *Binomial*.)
:::

:::proofen
Induction, now over a list: `induction' l with y l ih` leaves the case `[]`, and the case `y :: l`
with the hypothesis `ih` for `l`. New: `List.length_cons : (y :: l).length = l.length + 1`.
:::

:::proofde
Induktion, jetzt über eine Liste: `induction' l with y l ih` lässt den Fall `[]`, und den Fall
`y :: l` mit der Annahme `ih` für `l`. Neu: `List.length_cons : (y :: l).length = l.length + 1`.
:::
:::solution
```
induction' l with y l ih
rw [List.length_nil, seq_zero_nil, List.count_nil, List.count_nil]
ring
rw [List.length_cons, seq_succ_apply, ih, mass_cons]
```
:::
::::

::::leanonly (proof := "(p : I) (n : ℕ) : binom p n = (iidSequence n (coin p)).map (fun l => l.count true)") (lemma := "binom_eq_count") (group := "chance.count") (uses := "seq_zero, map_pure, binom_zero, binom_succ, seq_succ, map_bind, bind_map_left, count_true_cons, induction', rfl, rw, simp_rw")
:::en
*Boss: binom counts.* `binom p n` was defined by recursion, one coin and then the rest. It is what one thinks: throw $`n` coins and count the `true`.
:::

:::de
*Endgegner: binom zählt.* `binom p n` war durch Rekursion definiert, eine Münze und dann der Rest. Es ist, was man denkt: Wirf $`n` Münzen und zähl die `true`.
:::
:::solution
```
induction' n with n ih
rw [seq_zero, map_pure, binom_zero]
rfl
rw [binom_succ, seq_succ, ih]
simp_rw [map_bind, map_pure, bind_map_left, count_true_cons]
```
:::
::::
