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
proposals of the first version of this file are carried out, and after them the thin tactics got
their levels (see the end); "open" is what is left. 14 worlds, 165 levels.

## 1. Bool (15 levels)

**Goal.** A circuit is a function, and a function on `Bool` is its truth table: two circuits are
equal when all rows agree.

**Tactics.** `rfl`, `rw`, `cases`, `<;>`.

**Path.** One input, read off (`rfl`). Rewriting with what is already proved (`rw`). One input,
both cases (`cases`). The `bif` rules. A quiz on `cases x <;> rfl`. Two inputs, four cases
(De Morgan). Boss: xor from `and`, `or`, `not`, with its table.

**Open.** The boss has the same proof line as De Morgan before it; it is harder on the board only.

## 2. Masses (14 levels)

**Goal.** A distribution on `Bool` is two masses that add up to 1, and a map moves each mass to its
image (`map_true`).

**Tactics.** `rw` in chains (practised here), `constructor`, `exact`, `apply` (first contact).

**Path.** The masses of the coin, and both in one statement (`∧`, `constructor`). Sums over `Bool`
and point tests (`==`). Where the mass goes (`map_apply`, then `map_true`). The whole mass; for the
coin, by `exact mass_total (coin p)`: a theorem with its argument. At most one, finite. Boss:
`((coin p).map not) true = σ p`, on the board.

**Open.** `apply` meets the player first on `≠ ⊤`: a new tactic and a new kind of statement at once.
*At most one* and *Finite* serve the subtraction in *One Coin*.

## 3. One Coin (14 levels)

**Goal.** One number fixes a distribution on `Bool` (`bool_ext`): every distribution on `Bool` is a
coin, and a flipped coin is the coin `σ p`.

**Tactics.** `apply bool_ext`, `exact h`; `ext` (once).

**Path.** The rest of the mass. One bar is enough (`bool_ext`), and at once its shortest use
(`eq_coin`). Sure outcomes (`pure`, `coin_const`, `map_pure`), both masses of `pure true` with
`constructor`. Boss: `coin_not`.

## 4. Maps (8 levels)

**Goal.** Two moves are one move (`map_map`). A statement about an unknown `f : Bool → Bool` is
settled by the four maps, or by `f true` and `f false`.

**Tactics.** `revert` and `decide`, `simp_rw` (rewriting under `fun`), `cases f true`.

**Path.** Three times `f`. A quiz: which statements hold for every `f` (`revert f b; decide`).
Doing nothing (`map_id`). A quiz: where does `rw` fail (under `fun`)? Flipped twice with `simp_rw`. A test is `true` or `false`
(`cases f true`, on its own). Two masses behind one test. Boss: `map_map`, used at once on the
first board of *Laws of `do`*.

**Open.** No board in the world itself. `cond_add_cond` and `Bool.apply_apply_apply` are not used
again.

## 5. Two Coins (8 levels)

**Goal.** A circuit with a coin at each input is a `do` block. Along a row the masses of the coins
multiply, over the rows they add (`bind_true`): both `true` is `coin (p * q)`.

**Tactics.** `simp` (the game's), `ring`.

**Path.** A board first: one draw, used twice (`bind_pure`). `do` is `bind`; `bind_true`. The
simplifier on a board (at least one `true`, two ways) and its quiz. `coin_and`. The same product
twice (`ring`). Boss: exactly one `true`, its mass computed.

## 6. Laws of `do` (13 levels)

**Goal.** A circuit is rebuilt, not computed: three laws between moves and draws, and a coin that
is not used.

**Tactics.** `congr`; `cases f true <;> cases f false` for the laws; `simp_rw` under bound names.

**Path.** A board: flipped twice, by `map_map`. Each law (`map_eq_pure_bind`, `bind_map_left`,
`map_bind`, `coin_unused`), proved on `Bool` and then used on a board, in one line (a gate is a
draw; the gate at the end; one coin too many). Boss: at least one `true`
is `coin (σ (σ p * σ p))`, from `coin_not`, `coin_and` and De Morgan, without computing a mass.

**Open.** The laws are stated for general `μ`, `f`, `g`; only the first has its instance on a
board before it.

## 7. Counting (15 levels)

**Goal.** `binom p n` is the number of `true` among `n` coins, built one coin at a time; and
counts add: `B(n, p)` and `B(m, p)` give `B(n + m, p)`.

**Tactics.** `simp_rw` with `pure_bind`, `bind_assoc`; `induction'`.

**Path.** `toNat`. `binom_zero`, `binom_succ`. Two and three coins are `binom p 2`, `binom p 3`; a
quiz on which circuits are `binom`. The majority of three. A first induction with a one-line step:
a coin that never shows `true` (`binom_never`). The coin at the other end (`binom_succ'`). Boss:
`binom_add`.

**Open.** One level with a gap.

## 8. Multi-Stage Experiments (15 levels)

**Goal.** Two-stage experiments: which coin is thrown second depends on the first. The mass of the
result is the sum over the two ways, `p · q + (1 − p) · r` (total probability).

**Tactics.** `rw [bind_true]`, then `simp`: the standard computation of the game.

**Path.** The `bind` gate without coins. Waiting coins on the board. The same in general, at
`true` and at `false`, with gaps for the masses. A distribution that stays. Forgetting. Boss:
three tries.

**Open.** The boss has the same proof as *A chain*.

## 9. Balance (10 levels; before: Real Numbers)

**Goal.** When does a waiting coin leave `coin p` unchanged? In balance,
`(1 − p) · r = p · (1 − q)` (`coin_stays`). To use such an equation, the masses are taken from
`[0, ∞]` to `ℝ`.

**Tactics.** `ring` (once more), `linear_combination`, `field_simp`.

**Path.** A mass as a real number; products; sums. `linear_combination`: twice a hypothesis, the
balance in `ℝ` (the lemma `balance`), two hypotheses (a gap: how much lies at `true`?). Fractions:
shares add up to one (`field_simp`), and which coin is in balance (a gap: `p = r / (r + 1 − q)`).
Boss: `coin_stays`, ending with `apply balance`, `exact h`; used again in *Hypergeometric*.

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

**Open.** It opens with tool levels before the question is posed.

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

**Open.** Clear; the place where both ways (*Counting*, *Multi-Stage Experiments*) meet.

## 14. Hypergeometric (14 levels)

**Goal.** Drawing without putting back: each draw is a waiting coin whose chance is the share of
white balls left. And still the second ball is white as often as the first.

**Tactics.** `simp` with lemmas given by hand, `induction'` with `generalizing`, `field_simp`,
`apply coin_stays`, `linear_combination`.

**Path.** `hyper_zero`; `hyper_succ` with gaps for the urn after a white ball. One draw, white and
black. One of each: the first mass with both colours, as a gap. The edges: only black, only white,
all balls. The share of black (`frac_real`, `field_simp`). Put back: the second ball as the first
(`apply coin_stays`), and two colours (`linear_combination`, a gap). Boss: the second ball, not put
back: a balance.

**Open.** No board. The general mass (with binomial coefficients) is not there.

## Across the worlds

**Bosses.** Every world ends with its boss, and no boss has a tip.

**Tips are minimal.** The text of a proof is what 💡 shows, so it names the idea, a new rule with
its statement, or a new tactic and what it does: never the sequence of tactics, and never the
answer to a gap. No level has a folded *Tip* line any more (before: 29, and 113 of 129 before
that). A tactic is written with its arguments only in the level that introduces it.
A new tactic with a tip of its own shows only that tip, not the card of the tactic.

**Tactics per world.** A world has the tactics that its levels use (their solutions and quizzes,
written into `uses` by `tests/uses.py`), as far as earned; `rfl`, `exact`, `rw`, `cases` and `ring`
stay in every world once earned. So `linear_combination` and `field_simp` are there only in Balance
and Hypergeometric, `revert` and `decide` only in Maps and Multi-Stage Experiments.

**Questions.** Levels with a gap in the statement, only in Lean levels (on a board the answer can be read
off the board): Bool 3, Masses 6, One Coin 10, Maps 6, Two Coins 1, Laws of `do` 5, Counting 1, Balance 3, Sequences 1, Binomial 2, Geometric 6, Thinning 2, Hypergeometric 6. Five quizzes.

**Tactics: three meetings.** A tactic is introduced (its text says what it does), practised in its world,
and used again in a later world. `python3 tests/tactics.py` counts, from the solutions, the levels
and worlds of each tactic, and fails when one occurs in fewer than three levels or in one world only.
Its table now:

| tactic | introduced | levels, by world | weak point |
|---|---|---|---|
| `rfl`, `rw`, `cases`, `<;>` | Bool | everywhere | none |
| `constructor` | Masses | Masses 1, One Coin 1, Binomial 2 | four levels |
| `exact` | Masses | Masses 3, One Coin 1, Multi-Stage Experiments 1, Balance 1, Thinning 1 | none; a theorem with its argument only twice |
| `apply` | Masses | One Coin 4, Hypergeometric 2, five worlds 1 each | mostly `bool_ext`; now also `balance`, `coin_stays` twice |
| `ext` | One Coin | Laws of `do` 6, Maps 2, Counting 2, three worlds 1 | none |
| `revert`, `decide` | Maps | Maps 2, Multi-Stage Experiments 3 | two worlds |
| `simp_rw` | Maps | Laws of `do` 4, Maps 3, Two Coins 1 | used on to the end; `simp only` is not given (it would do the same) |
| `simp` | Two Coins | 31 levels in 9 worlds | none |
| `congr` | Laws of `do` | Laws of `do` 2, Counting 2, Balance 1, Thinning 1 | none |
| `ring` | Two Coins | 14 levels in 6 worlds | none |
| `induction'` | Counting | 15 levels in 6 worlds | none |
| `linear_combination` | Balance | Balance 3, Hypergeometric 1 | one world after its own; none other follows *Balance* |
| `field_simp` | Balance | Balance 2, Hypergeometric 2 | the same |

When which of the three that rewrite: the inventory says it at each (`rw`: not under bound names;
`simp_rw`: there, in the order given; `simp`: computing).

## What was done (2026-11-22)

1. Fading tips, and no tip in a boss.
2. Bosses: *Masses* 12 marked; `eq_coin` before the boss in *One Coin*; `binom_add` the boss of
   *Counting*; *Building with Coins* split into *Two Coins* (boss: exactly one `true`) and
   *Laws of `do`* (boss: at least one `true`).
3. Gaps for the masses in *Multi-Stage Experiments*, *Geometric*, *Hypergeometric*.
4. *Geometric* from the waiting coin; *Hypergeometric* with one draw, one of each, and the boss
   *the second ball*.
5. A first, easy induction in *Counting* (`binom_never`); in *Maps* a quiz and a level for
   `cases f true`; a board for `map_map` in *Laws of `do`*.
6. *Sequences*: the mass of a list (`mass_cons`, `seq_mass`). *Real Numbers* is called *Balance*
   and is used by the boss of *Hypergeometric*.

Then, for the tactics that occurred too seldom:

7. *Balance*: two hypotheses for `linear_combination`; `field_simp` introduced here, on shares, and
   used for "which coin is in balance?"; the lemma `balance`, used by `apply` in the boss.
8. *Hypergeometric*: put back (`apply coin_stays`), two colours (`linear_combination`).
9. `constructor` introduced in *Masses* (both masses), practised in *One Coin*; `exact` introduced on
   an equation (`exact mass_total (coin p)`, which proves `coin_total`).
10. *Maps*: a quiz, where `rw` fails. `tests/tactics.py`: three meetings.
