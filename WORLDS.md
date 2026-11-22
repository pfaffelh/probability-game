# The worlds: what each one is for (state of 2026-11-22)

The game has reached its aim when the player

- **masters the tactics**: uses them without being told the line, and
- **knows how the distributions come about and why**: can say from which coins and gates a
  distribution is built, and where its masses come from.

A world is measured against four questions.

1. Can its goal be said in one sentence?
2. Is the boss that goal (and the hardest level, and the last)?
3. Does every level lead to the boss?
4. Is each new tactic introduced on an easy statement, practised, and then used without help?

For each world: its goal, the tactics, how the levels get there, and what is open. The six
proposals of the first version of this file are carried out (see the end); "open" is what is left.
14 worlds, 155 levels.

## 1. Bool (14 levels)

**Goal.** A circuit is a function, and a function on `Bool` is its truth table: two circuits are
equal when all rows agree.

**Tactics.** `rfl`, `rw`, `cases`, `<;>`.

**Path.** One input, read off (`rfl`). Rewriting with what is already proved (`rw`). One input,
both cases (`cases`). The `bif` rules. A quiz on `cases x <;> rfl`. Two inputs, four cases
(De Morgan). Boss: xor from `and`, `or`, `not`, with its table.

**Open.** The boss has the same proof line as De Morgan before it; it is harder on the board only.

## 2. Masses (12 levels)

**Goal.** A distribution on `Bool` is two masses that add up to 1, and a map moves each mass to its
image (`map_true`).

**Tactics.** `rw` in chains (practised here), `exact`, `apply` (first contact).

**Path.** The masses of the coin. Sums over `Bool` and point tests (`==`). Where the mass goes
(`map_apply`, then `map_true`). The whole mass, at most one, finite. Boss:
`((coin p).map not) true = σ p`, on the board.

**Open.** `exact` and `apply` meet the player first on `≤` and `≠ ⊤`: a new tactic and a new kind
of statement at once. *At most one* and *Finite* serve the subtraction in *One Coin*.

## 3. One Coin (13 levels)

**Goal.** One number fixes a distribution on `Bool` (`bool_ext`): every distribution on `Bool` is a
coin, and a flipped coin is the coin `σ p`.

**Tactics.** `apply bool_ext`, `exact h`; `ext` (once).

**Path.** The rest of the mass. One bar is enough (`bool_ext`), and at once its shortest use
(`eq_coin`). Sure outcomes (`pure`, `coin_const`, `map_pure`). Boss: `coin_not`.

## 4. Maps (7 levels)

**Goal.** Two moves are one move (`map_map`). A statement about an unknown `f : Bool → Bool` is
settled by the four maps, or by `f true` and `f false`.

**Tactics.** `revert` and `decide`, `simp_rw` (rewriting under `fun`), `cases f true`.

**Path.** Three times `f`. A quiz: which statements hold for every `f` (`revert f b; decide`).
Doing nothing (`map_id`). Flipped twice with `simp_rw`. A test is `true` or `false`
(`cases f true`, on its own). Two masses behind one test. Boss: `map_map`, used at once on the
first board of *Laws of `do`*.

**Open.** No board in the world itself. `cond_add_cond` and `Bool.apply_apply_apply` are not used
again.

## 5. Two Coins (8 levels)

**Goal.** A circuit with a coin at each input is a `do` block. Along a row the masses of the coins
multiply, over the rows they add (`bind_true`): both `true` is `coin (p * q)`.

**Tactics.** `simp` (the game's), `ring`.

**Path.** The simplifier and its quiz. `do` is `bind`; `bind_true`. `coin_and`. The same product
twice (`ring`). Boss: exactly one `true`, its mass computed.

## 6. Laws of `do` (10 levels)

**Goal.** A circuit is rebuilt, not computed: three laws between moves and draws, and a coin that
is not used.

**Tactics.** `simp only`, `congr`; `cases f true <;> cases f false` for the laws.

**Path.** A board: flipped twice, by `map_map`. Each law (`map_eq_pure_bind`, `bind_map_left`,
`map_bind`, `coin_unused`), proved on `Bool` and then used on a board. Boss: at least one `true`
is `coin (σ (σ p * σ p))`, from `coin_not`, `coin_and` and De Morgan, without computing a mass.

**Open.** The laws are stated for general `μ`, `f`, `g`; only the first has its instance on a
board before it.

## 7. Counting (15 levels)

**Goal.** `binom p n` is the number of `true` among `n` coins, built one coin at a time; and
counts add: `B(n, p)` and `B(m, p)` give `B(n + m, p)`.

**Tactics.** `simp only` with `pure_bind`, `bind_assoc`; `induction'`.

**Path.** `toNat`. `binom_zero`, `binom_succ`. Two and three coins are `binom p 2`, `binom p 3`; a
quiz on which circuits are `binom`. The majority of three. A first induction with a one-line step:
a coin that never shows `true` (`binom_never`). The coin at the other end (`binom_succ'`). Boss:
`binom_add`.

**Open.** One level with a gap.

## 8. Coins that Wait (15 levels)

**Goal.** Two-stage experiments: which coin is thrown second depends on the first. The mass of the
result is the sum over the two ways, `p · q + (1 − p) · r` (total probability).

**Tactics.** `rw [bind_true]`, then `simp`: the standard computation of the game.

**Path.** The `bind` gate without coins. Waiting coins on the board. The same in general, at
`true` and at `false`, with gaps for the masses. A distribution that stays. Forgetting. Boss:
three tries.

**Open.** The boss has the same proof as *A chain*.

## 9. Balance (7 levels; before: Real Numbers)

**Goal.** When does a waiting coin leave `coin p` unchanged? In balance,
`(1 − p) · r = p · (1 − q)` (`coin_stays`). To use such an equation, the masses are taken from
`[0, ∞]` to `ℝ`.

**Tactics.** `ring` (once more), `linear_combination`.

**Path.** A mass as a real number; products; sums. `linear_combination`. Boss: `coin_stays`, used
again by the boss of *Hypergeometric*.

**Open.** `linear_combination` occurs in three lines, all here.

## 10. Sequences (8 levels)

**Goal.** `n` throws are a list. Its mass depends only on its numbers of `true` and `false`
(`seq_mass`), and `binom p n` is the number of `true` in it (`binom_eq_count`).

**Tactics.** `induction'` over a list, `cases y`, `ring`.

**Path.** One throw as a list. The mass of `[true, false]` (a gap). Counting `true`, counting
`false`. The empty list. One more in front (`mass_cons`). The mass of a list (`seq_mass`). Boss:
`binom_eq_count`.

**Open.** `seq_mass` is the summit of the new levels, the boss is another statement; both stand.
The number of lists with `k` times `true` (`n.choose k`) is said in a text, not proved.

## 11. Binomial (14 levels)

**Goal.** The masses of `B(n, p)`: `binom p n k = n.choose k · p^k · (1 − p)^(n − k)`, from "one
coin more" (Pascal's rule for masses).

**Tactics.** `induction'` (also `generalizing`), long `rw` chains, `ring`, `constructor`.

**Path.** Tools (`coin_bind_apply`, `pure_self`, no throw, shift). The two recursions of the masses.
The edges. Pascal's triangle. Boss: the formula. Encore: `binom_symm`.

**Open.** It opens with tool levels before the question is posed. `constructor` occurs twice.

## 12. Geometric (11 levels)

**Goal.** Waiting for the first `true`: mass `(1 − p)^k · p` at `k`, no memory, total mass 1; and
the `do` block that waits (`geom_first`).

**Tactics.** `rw [bind_true]` and `simp`, `induction'`, `ring`, sums of series (`tsum`).

**Path.** From the waiting coin: the first `true` at the second throw, at the third (gaps for the
masses). Then `geom_zero`, `geom_succ` with gaps: the player says the definition. Three tries are
`geom p 0 + geom p 1 + geom p 2`. The formula and no memory, with gaps. The series and the total
mass. Boss: `geom_first`.

**Open.** No board.

## 13. Thinning (9 levels)

**Goal.** Keeping each `true` only with probability `q` keeps the family: a coin stays a coin, a
geometric stays geometric, a binomial stays binomial (`binom_thin`).

**Tactics.** Everything so far, together; `bind_comm`.

**Open.** Clear; the place where both ways (*Counting*, *Coins that Wait*) meet.

## 14. Hypergeometric (12 levels)

**Goal.** Drawing without putting back: each draw is a waiting coin whose chance is the share of
white balls left. And still the second ball is white as often as the first.

**Tactics.** `simp` with lemmas given by hand, `induction'` with `generalizing`, `field_simp`,
`apply coin_stays`.

**Path.** `hyper_zero`; `hyper_succ` with gaps for the urn after a white ball. One draw, white and
black. One of each: the first mass with both colours, as a gap. The edges: only black, only white,
all balls. The share of black (`frac_real`, `field_simp`). Boss: the second ball, a balance.

**Open.** No board. The general mass (with binomial coefficients) is not there.

## Across the worlds

**Bosses.** Every world ends with its boss, and no boss has a tip.

**Help fades.** 33 levels end with a *Tip* (before: 113 of 129): where a tactic or a method is
new. Elsewhere the text names the idea (which rule), not the line.

**Questions.** Levels with a gap in the statement: Bool 8, Masses 6, One Coin 10, Maps 6, Two
Coins 2, Laws of `do` 5, Counting 1, Coins that Wait 6, Balance 0, Sequences 1, Binomial 2,
Geometric 6, Thinning 5, Hypergeometric 5. Four quizzes.

**Tactics.** Lines of the solutions in which each tactic occurs.

| tactic | introduced | lines, by world | weak point |
|---|---|---|---|
| `rfl`, `rw`, `cases`, `<;>` | Bool | everywhere | none |
| `exact` | Masses | Masses 3, One Coin 1, Coins that Wait 1, Thinning 1 | six lines in the game; twice `exact h` |
| `apply` | Masses | One Coin 4, six worlds 1 each | nine times `bool_ext`, once `coin_stays`, once on `≠ ⊤` |
| `ext` | One Coin | Laws of `do` 7, Counting 4, Maps 2, three worlds 1 | none |
| `revert`, `decide` | Maps | Maps 1 and a quiz, Coins that Wait 3 | thin |
| `simp_rw` | Maps | Maps 11, Laws of `do` 4, Two Coins 1 | gone after *Laws of `do`*; when it, when `simp only`? |
| `simp` | Two Coins | 30 lines in 8 worlds | none |
| `simp only` | Laws of `do` | 22 lines in 7 worlds | none |
| `congr` | Laws of `do` | Counting 4, Laws of `do` 3, Balance 1, Thinning 1 | none |
| `ring` | Two Coins | Sequences 4, Binomial 3, Two Coins 2, Hypergeometric 2, Balance 1, Geometric 1 | none now |
| `induction'` | Counting | Binomial 5, Hypergeometric 4, Counting 3, Sequences 2, Geometric 2, Thinning 1 | none now |
| `linear_combination` | Balance | Balance 3 | never again |
| `constructor` | Binomial | Binomial 2 | never again |
| `field_simp` | Hypergeometric | Hypergeometric 2 | new and last |

## What was done (2026-11-22)

1. Fading tips, and no tip in a boss.
2. Bosses: *Masses* 12 marked; `eq_coin` before the boss in *One Coin*; `binom_add` the boss of
   *Counting*; *Building with Coins* split into *Two Coins* (boss: exactly one `true`) and
   *Laws of `do`* (boss: at least one `true`).
3. Gaps for the masses in *Coins that Wait*, *Geometric*, *Hypergeometric*.
4. *Geometric* from the waiting coin; *Hypergeometric* with one draw, one of each, and the boss
   *the second ball*.
5. A first, easy induction in *Counting* (`binom_never`); in *Maps* a quiz and a level for
   `cases f true`; a board for `map_map` in *Laws of `do`*.
6. *Sequences*: the mass of a list (`mass_cons`, `seq_mass`). *Real Numbers* is called *Balance*
   and is used by the boss of *Hypergeometric*.
