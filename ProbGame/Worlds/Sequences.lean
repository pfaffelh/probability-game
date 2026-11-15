import VersoManual
import ProbGame.Level

open Verso.Genre Manual
open ProbGame

#doc (Manual) "Sequences" =>

%%%
htmlSplit := .never
%%%

:::en
Throwing $`n` coins one after the other gives a list of $`n` outcomes: `iidSequence n (coin p)`, a distribution on lists (independent, identically distributed). The boss: `binom p n` is the number of `true` in it. In Lean only.
:::

:::de
$`n` Münzen nacheinander werfen ergibt eine Liste von $`n` Ergebnissen: `iidSequence n (coin p)`, eine Verteilung auf Listen (unabhängig, identisch verteilt). Der Endgegner: `binom p n` ist die Anzahl der `true` darin. Nur in Lean.
:::

::::leanonly (proof := "(p : I) : iidSequence 1 (coin p) = (do let y ← coin p; pure [y])") (new := "seq_zero, seq_succ") (group := "chance.count")
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

*Tip.* `rw [seq_succ, seq_zero]`, `simp only [pure_bind]`.
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

*Tipp.* `rw [seq_succ, seq_zero]`, `simp only [pure_bind]`.
:::
:::solution
```
rw [seq_succ, seq_zero]
simp only [pure_bind]
```
:::
::::

::::leanonly (proof := "(p : I) : iidSequence 2 (coin p) [true, false] = ↑p * ↑(σ p)") (new := "seq_succ_apply, seq_zero_nil, mul_one") (group := "chance.count")
:::en
*The mass of a sequence.* Independent: the mass of a list is the product of the masses of its entries. First `true`, then `false`: $`p (1 - p)`.
:::

:::de
*Die Masse einer Folge.* Unabhängig: Die Masse einer Liste ist das Produkt der Massen ihrer Einträge. Erst `true`, dann `false`: $`p (1 - p)`.
:::

:::proofen
`seq_succ_apply : iidSequence (n + 1) μ (a :: l) = μ a * iidSequence n μ l` and `seq_zero_nil : iidSequence 0 μ [] = 1` (`[true, false]` is `true :: false :: []`).

*Tip.* `rw [seq_succ_apply, seq_succ_apply, seq_zero_nil, mul_one, coin_true, coin_false]`.
:::

:::proofde
`seq_succ_apply : iidSequence (n + 1) μ (a :: l) = μ a * iidSequence n μ l` und `seq_zero_nil : iidSequence 0 μ [] = 1` (`[true, false]` ist `true :: false :: []`).

*Tipp.* `rw [seq_succ_apply, seq_succ_apply, seq_zero_nil, mul_one, coin_true, coin_false]`.
:::
:::solution
```
rw [seq_succ_apply, seq_succ_apply, seq_zero_nil, mul_one, coin_true, coin_false]
```
:::
::::

::::leanonly (proof := "(l : List Bool) : (true :: l).count true = 1 + l.count true") (new := "count_true_cons, Bool.toNat_true") (group := "chance.count")
:::en
*Counting true.* `l.count true` is the number of `true` in the list `l`. One in front counts as its number, `toNat`.
:::

:::de
*true zählen.* `l.count true` ist die Anzahl der `true` in der Liste `l`. Eins vorne zählt mit seiner Zahl, `toNat`.
:::

:::proofen
`count_true_cons : (y :: l).count true = y.toNat + l.count true`.

*Tip.* `rw [count_true_cons, Bool.toNat_true]`.
:::

:::proofde
`count_true_cons : (y :: l).count true = y.toNat + l.count true`.

*Tipp.* `rw [count_true_cons, Bool.toNat_true]`.
:::
:::solution
```
rw [count_true_cons, Bool.toNat_true]
```
:::
::::

::::leanonly (proof := "(p : I) (n : ℕ) : binom p n = (fun l => l.count true) <$> iidSequence n (coin p)") (lemma := "binom_eq_count") (group := "chance.count")
:::en
*Boss: binom counts.* `binom p n` was defined by recursion, one coin and then the rest. It is what one thinks: throw $`n` coins and count the `true`.
:::

:::de
*Endgegner: binom zählt.* `binom p n` war durch Rekursion definiert, eine Münze und dann der Rest. Es ist, was man denkt: Wirf $`n` Münzen und zähl die `true`.
:::

:::proofen
Induction on $`n`. At $`0` both sides are `pure 0` once `([] : List Bool).count true` is computed: `rfl`. In the step `binom_succ`, `seq_succ` and `ih`; then the move `count` goes into the `do` block (`map_bind`, `map_pure`, `bind_map_left`, from *Building with Coins*), and `count_true_cons` counts the first.

*Tip.* `induction' n with n ih`; `rw [seq_zero, map_pure, binom_zero]`, `rfl`; `rw [binom_succ, seq_succ, ih]`, `simp only [map_bind, map_pure, bind_map_left, count_true_cons]`.
:::

:::proofde
Induktion über $`n`. Bei $`0` sind beide Seiten `pure 0`, sobald `([] : List Bool).count true` ausgerechnet ist: `rfl`. Im Schritt `binom_succ`, `seq_succ` und `ih`; dann geht der Zug `count` in den `do`-Block (`map_bind`, `map_pure`, `bind_map_left`, aus *Bauen mit Münzen*), und `count_true_cons` zählt das erste.

*Tipp.* `induction' n with n ih`; `rw [seq_zero, map_pure, binom_zero]`, `rfl`; `rw [binom_succ, seq_succ, ih]`, `simp only [map_bind, map_pure, bind_map_left, count_true_cons]`.
:::
:::solution
```
induction' n with n ih
rw [seq_zero, map_pure, binom_zero]
rfl
rw [binom_succ, seq_succ, ih]
simp only [map_bind, map_pure, bind_map_left, count_true_cons]
```
:::
::::
