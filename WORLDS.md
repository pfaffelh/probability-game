# The worlds: what each one is for (planning, 2026-11-22)

The game has reached its aim when the player

- **masters the tactics**: uses them without being told the line, and
- **knows how the distributions come about and why**: can say from which coins and gates a
  distribution is built, and where its masses come from.

A world is measured against four questions.

1. Can its goal be said in one sentence?
2. Is the boss that goal (and the hardest level)?
3. Does every level lead to the boss?
4. Is each new tactic introduced on an easy statement, practised, and then used without help?

For each world: its goal, what the player can do afterwards, how the levels get there, and what is
open. "Open" is a proposal, not a decision. Nothing in the levels has been changed for this file.

## 1. Bool (14 levels)

**Goal.** A circuit is a function, and a function on `Bool` is its truth table: two circuits are
equal when all rows agree.

**Tactics.** `rfl`, `rw`, `cases`, `<;>`.

**Path.** One input, read off (`rfl`). Rewriting with what is already proved (`rw`). One input,
both cases (`cases`). The `bif` rules. A quiz on `cases x <;> rfl`. Two inputs, four cases
(De Morgan). Boss: xor from `and`, `or`, `not`, with its table.

**Open.** The goal is clear and the boss is the goal. The boss has the same proof line as De Morgan
before it; it is harder on the board only. `rw` is used in two levels here; it is practised in
*Masses*.

## 2. Masses (12 levels)

**Goal.** A distribution on `Bool` is two masses that add up to 1, and a map moves each mass to its
image (`map_true`).

**Tactics.** `rw` in chains (practised here), `exact`, `apply` (first contact).

**Path.** The masses of the coin (`coin_true`, `coin_false`). Sums over `Bool` and point tests
(`==`). Where the mass goes (`map_apply`, then `map_true`). The whole mass (`mass_total`), at most
one, finite. Last level: `((coin p).map not) true = σ p`, on the board.

**Open.**
- No level is marked as the boss. The last level is the goal; mark it.
- *At most one* and *Finite* (levels 10, 11) serve the subtraction in *One Coin*, not this goal.
  They could open *One Coin*.
- `exact` and `apply` meet the player first on `≤` and `≠ ⊤`: a new tactic and a new kind of
  statement at once.

## 3. One Coin (13 levels)

**Goal.** One number fixes a distribution on `Bool`: two distributions with the same mass at `true`
are equal (`bool_ext`). So every distribution on `Bool` is a coin, and a flipped coin is the coin
`σ p`.

**Tactics.** `apply bool_ext` as the way to prove that two distributions are equal; `ext` (once).

**Path.** The rest of the mass (`mass_not`). One bar is enough (`bool_ext`). Sure outcomes (`pure`,
`coin_const`, `map_pure`). Boss: `coin_not`. After it: `eq_coin`.

**Open.** `eq_coin` is the shortest use of `bool_ext` (two lines) and stands after the boss. Put it
right after `bool_ext`: the easiest application first, the boss last.

## 4. Maps (5 levels)

**Goal.** Two moves are one move (`map_map`). A statement about an unknown `f : Bool → Bool` is
settled by `f true` and `f false`.

**Tactics.** `simp_rw` (rewriting under `fun`), `cases f true`, `revert` and `decide`.

**Path.** Three times `f`. Doing nothing (`map_id`). Flipped twice with `simp_rw`. Two masses
behind one test. Boss: `map_map`.

**Open.**
- The thinnest world: no board, no quiz, and `map_map`, `cond_add_cond`, `Bool.apply_apply_apply`
  are never used again. What stays is the method `cases f true <;> cases f false`, which the laws
  in *Building with Coins* need.
- That method is the new idea of the world and has no level of its own; it first appears inside
  level 4 together with `simp_rw`.
- `revert`, `decide` come in level 1 and return only in *Coins that Wait* (levels 1 to 3).
- Candidates: a quiz "which statements hold for every `f`" (`revert f b; decide`), so the player
  goes through the four maps; a board "flipped twice" proved with `map_map`, so the boss is used.

## 5. Building with Coins (15 levels)

**Goal.** A circuit with a coin at each input is a `do` block. Its masses: along a row the masses
of the coins multiply, over the rows they add (`bind_true`). Results: both `true` is `coin (p * q)`,
at least one `true` is `coin (σ (σ p * σ p))`.

**Tactics.** `simp` (the game's), `simp only`, `congr`.

**Path.** The simplifier and its quiz. `do` is `bind`; `bind_true`. `coin_and`. The laws between
`map` and `bind` (`map_eq_pure_bind`, `bind_map_left`, `map_bind`, `coin_unused`), each followed by
a circuit that uses it. `congr`. Boss: xor, as an equation of two circuits.

**Open.**
- Four themes in one world: the simplifier, the product rule, the laws of `do`, `congr`.
- The boss says that two circuits with the same table have the same distribution. It does not say
  what the distribution of xor is, and its proof is easier than the three law levels.
- The level that uses everything is *At least one `true`* (level 11): `coin_not`, `coin_and`,
  `bind_map_left`, `map_bind`, `map_pure` and De Morgan from *Bool*. It is the natural boss.
- A split is possible. *Two Coins*: simplifier, `do`, `bind_true`, `coin_and`, boss the mass of xor
  (`2p(1 − p)`), computed. *Laws of `do`*: the three laws, `coin_unused`, `congr`, boss *At least
  one `true`*, rebuilt from known coins without computing.
- The three laws are stated for general `μ`, `f`, `g` before the player has seen one instance.
  A board before each (already proposed) gives the instance.

## 6. Counting (14 levels)

**Goal.** `binom p n` is the number of `true` among `n` coins, built one coin at a time; and
counts add: `B(n, p)` and `B(m, p)` give `B(n + m, p)`.

**Tactics.** `simp only` with the laws of `do` (`pure_bind`, `bind_assoc`), `induction'`.

**Path.** `toNat`. `binom_zero`, `binom_succ`. Two coins and three coins are `binom p 2`,
`binom p 3`; a quiz on which circuits are `binom`. The coin at the other end (`binom_succ'`).
`binom_add`. Boss: the majority of three.

**Open.**
- The summit of the line is `binom_add` (level 13). The majority is an application of `binom p 3`
  beside the line: make `binom_add` the boss and put the majority after *Three coins*.
- `induction'` is introduced on `binom_succ'`, the hardest computation so far. A first induction
  with a one-line step is missing (a coin that never shows `true`: the count is surely 0).
- One level with a gap.

## 7. Coins that Wait (15 levels)

**Goal.** Two-stage experiments: which coin is thrown second depends on the first. The mass of the
result is the sum over the two ways, `p · q + (1 − p) · r` (`bind_true`, total probability).

**Tactics.** `rw [bind_true]`, then `simp`: the standard computation of the game.

**Path.** The `bind` gate without coins. Waiting coins on the board: only after `true`, copying,
one more try, a coin that remembers, a chain. The same in general (`p`, `q`, `r`), at `true` and at
`false`. A distribution that stays. Forgetting. Boss: three tries.

**Open.**
- The clearest goal and the most boards. But seven levels have the same two proof lines
  (`rw [bind_true]`, `simp`), and the mass is given in the statement: nothing is left to predict. Gaps for the masses (levels 4 to 8 and
  the boss) put the thinking where the goal is.
- The boss has the same proof as *A chain* (level 8).
- *A distribution that stays* prepares *Real Numbers*; *Forgetting* stands alone.

## 8. Real Numbers (7 levels)

**Goal.** When does a waiting coin leave `coin p` unchanged? Exactly in balance:
`(1 − p) · r = p · (1 − q)`, as much mass goes from `false` to `true` as back (`coin_stays`). To
solve such equations, the masses are moved from `[0, ∞]` to `ℝ`.

**Tactics.** `ring`, `linear_combination`.

**Path.** A mass as a real number; products; sums. `ring`. `linear_combination`. Boss:
`coin_stays`.

**Open.**
- The title names the tool, the goal is the balance. The world's text should say so.
- `coin_stays` and `linear_combination` are never used again; `ring` twice in *Binomial*. Either
  the world is called an excursion, or it gets a use: an example after the boss (given `q`, `r`:
  which `p` stays? as a gap), or the second draw in *Hypergeometric*.

## 9. Sequences (4 levels)

**Goal.** `n` throws are a list, and `binom p n` is the number of `true` in it
(`binom_eq_count`): the recursion of *Counting* really counts.

**Tactics.** `induction'` once more.

**Path.** One throw as a list. The mass of `[true, false]`. Counting `true` in a list. Boss:
`binom_eq_count`.

**Open.**
- Four levels and no result of its own beyond the boss.
- Here the *why* of the binomial coefficient is missing: a list with `k` times `true` has mass
  `p^k · (1 − p)^(n − k)`, whatever the order; and there are `n.choose k` such lists. One level
  with the mass of a general list gives the world its own goal and *Binomial* its second reading.

## 10. Binomial (11 levels)

**Goal.** The masses of `B(n, p)`: `binom p n k = n.choose k · p^k · (1 − p)^(n − k)`, from "one
coin more" (Pascal's rule for masses).

**Tactics.** `induction'` (also `generalizing`), long `rw` chains, `ring`; `constructor`.

**Path.** Tools (`coin_bind_apply`, `pure_self`, no throw, shift). The two recursions of the masses.
The edges: all `false`, above `n`, all `true`. Boss: the formula. Encore: `binom_symm`.

**Open.** The best-built world. It opens with four tool levels before the question is posed; a
board first (Pascal with masses, already proposed) states the goal before the tools.

## 11. Geometric (8 levels)

**Goal.** Waiting for the first `true`: mass `(1 − p)^k · p` at `k`, no memory, total mass 1; and
the `do` block that waits (`geom_first`).

**Tactics.** `induction'`, sums of series (`tsum`).

**Path.** `geom_zero`, `geom_succ` (the definition). The formula. Without memory. The geometric
series and the total mass. Boss: `geom_first`.

**Open.**
- The order is the reverse of "how it comes about": `geom` is defined by its masses, and the
  waiting comes last, as an equation. No board, no gap.
- The start is already built: the boss of *Coins that Wait* (three tries) is
  `geom p 0 + geom p 1 + geom p 2`. Two or three opening levels "first `true` at throw 0, 1, 2",
  with gaps, make `geom_succ` a thing the player has seen before it is defined.

## 12. Thinning (7 levels)

**Goal.** Keeping each `true` only with probability `q` keeps the family: a coin stays a coin
(`p · q`), a geometric stays geometric, a binomial stays binomial (`binom_thin`).

**Tactics.** Everything so far, together; `bind_comm`.

**Path.** `coin_thin`. The order does not matter. Thinning twice. Waiting for a kept `true`.
Thinning counted, for one coin. Boss: `binom_thin`.

**Open.** Clear; the summit of the game, and the place where both ways (*Counting*, *Coins that
Wait*) meet.

## 13. Hypergeometric (7 levels)

**Goal.** Drawing without putting back: each draw is a waiting coin whose chance is the share of
white balls left in the urn.

**Tactics.** `induction'` with `generalizing`.

**Path.** `hyper_zero`, `hyper_succ` (the definition). Only black. Only white. Boss: all balls
drawn gives `pure w`.

**Open.**
- How the distribution comes about is given (`hyper_succ` by `rfl`), not built: a gap for the two
  urns after the draw makes the player say it.
- No mass with both colours is ever computed; the boss is a check, not the distribution.
- Candidates: one draw (`hyper w b 1`); two white in two draws; and as the boss *the second ball is
  white as often as the first*, which is `coin_stays` from *Real Numbers* with the urn's numbers.

## Across the worlds

**Bosses.** The goal and the hardest level: *Bool*, *Maps*, *Real Numbers*, *Sequences*,
*Binomial*, *Geometric*, *Thinning*. Not marked: *Masses*. Not last: *One Coin*. Beside the goal:
*Building with Coins*, *Counting*. No harder than a level before: *Coins that Wait*. Too little:
*Hypergeometric*.

**Tactics.** Lines of the solutions in which each tactic occurs, by world.

| tactic | introduced | practised | weak point |
|---|---|---|---|
| `rfl`, `rw`, `cases`, `<;>` | Bool | everywhere | none |
| `exact` | Masses | 6 lines in the game | hardly practised |
| `apply` | Masses | almost only `apply bool_ext` | an idiom, not a tactic |
| `ext` | One Coin | Maps, Building with Coins, Counting | none |
| `revert`, `decide` | Maps | Coins that Wait 1 to 3 | a black box, used 4 times |
| `simp_rw` | Maps | Building with Coins, then gone | next to `simp only` and `simp`: when which? |
| `simp`, `simp only` | Building with Coins | everywhere after | none |
| `congr` | Building with Coins | Counting | none |
| `induction'` | Counting | Binomial, Geometric, Hypergeometric | first use too hard |
| `ring` | Real Numbers | Binomial (2) | thin |
| `linear_combination` | Real Numbers | never again | not consolidated |
| `constructor` | Binomial | never again | one use |

**The tip gives the proof.** In about nine of ten proof levels (113 of 129, counted by script) the
text of the level ends with a *Tip* that has every line of the solution, the bosses included. A
player can finish the game by copying. For "masters the tactics" the help has to fade: the full
line where a tactic is new; the idea only (which rule, not which line) when it returns; nothing
line by line in a boss, or only after a failed try. The quiz ("which statements does this line
prove?") tests a tactic without giving it; there are three.

**The second half has no questions.** From *Coins that Wait* on, almost no statement has a gap
(*Thinning* excepted), and *Real Numbers*, *Sequences*, *Geometric*, *Hypergeometric* have no
board. The formula is given and then proved. A gap for the mass makes the player predict it first,
and the prediction is the "why".

## Proposals, in the order I would take them

1. Fading tips, and no full tip in a boss.
2. Bosses: mark *Masses* 12; `eq_coin` before the boss in *One Coin*; `binom_add` as the boss of
   *Counting*; *At least one `true`* as the boss of *Building with Coins* (or the split).
3. Gaps for the masses in *Coins that Wait*, *Geometric*, *Hypergeometric*.
4. *Geometric* from the waiting coin; *Hypergeometric* with a mass of both colours.
5. A first, easy induction in *Counting*; a level for `cases f true` in *Maps*.
6. *Sequences*: the mass of a list. *Real Numbers*: named by its goal, and used once more.
