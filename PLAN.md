# Plan: from the first level to world 4 (2026-11-14)

The motto: **first building blocks, then more and more Lean.** Lean is mandatory in every level
(the proof is the second half of each level), but early on it is short and leans on the board;
later the board becomes an experiment table and Lean says "for all".

Fixed rules (from the discussion):

- A board is solved exactly when Target = Output. Structure is forced by gates and wires the level
  starts with (`start`), never by hidden extra conditions.
- Clicking the inventory only fills the input line; Run or Enter sends it.
- Everything a solution uses is introduced in an earlier level (or the level itself) of the same
  inventory group (`bool` for world ∧, `chance` for worlds 1 to 4). Checked by a script over the
  `:::solution` blocks.

## World ∧ — Circuits (board leads, Lean is one or two lines)

The Lean statement of a circuit level is now **your circuit = the target table, as a function by
cases**, e.g. `(x && y) = (fun | false, false => false | false, true => false | true, false => false
| true, true => true) x y`. The table on the board and the right side in Lean are the same thing.
No more `x && y = x && y`.

| # | level | board | Lean | new |
|---|---|---|---|---|
| 1 | A wire | x → output | `x = x`, `rfl` | `rfl` (equality) |
| 2 | Not true | true → not | `(!true) = false`, `rfl` | `rfl` reduces |
| 3 | Flipped twice | one not given | `!(!x) = x`: `cases x`, `rfl`, `rfl` | `cases`, lemma `Bool.not_not` |
| 4 | Always true, without always true | x twice | `cases x <;> rfl` | `<;>` |
| 5 | Both (and) | two inputs | `cases x <;> cases y <;> rfl` | |
| 6 | De Morgan | or from and, not | `decide +revert` | `decide` |
| 7–8 | xor, same | | `<;>` or `decide` | |
| 9–11 | bind (and, xor, if-then) | the bind gate | table again | |
| 12–13 | the map f | f given | `rw [h, h]`; `decide +revert` | `rw` |
| 14–16 | numbers, count, majority | toNat, plus | table with numbers | |

(4 and 5 swap: `<;>` comes with one input, then is needed with two.)
Lean texts added: how to read a statement (`example`, hypotheses, `:`, the goal after `⊢`), why the
table is written `fun | … => …` (and Lean shows it as `match`).

Later, not yet (the user's wish): Lean-only levels `x = true ∨ x = false` and the four maps
`Bool → Bool` at the end of this world.

## World 1 — One Coin (one coin, top to bottom; Lean grows)

All boards top to bottom as in world ∧: the coin `x ← coin p` above, gates, the output box below
with a small histogram (target dashed, output filled) and the masses `p`, `1 - p`. New gates:
*always T*, *always F* (the constant maps; `heads`/`tails` of the old bars).

| # | level | Lean | new |
|---|---|---|---|
| 1 | Where does the mass go? (not) | mass at true: `coin_not_true` | `rw`, `map_true`, `coin_true`, … |
| 2 | What is not at true (Lean only) | `mass_false` | `mass_total`, `mass_ne_top`, `ENNReal.add_sub_cancel_left`, `exact` |
| 3 | What is not at false (Lean only) | `mass_true` | `add_comm` |
| 4 | One bar is enough (Lean only) | `bool_ext` | `ext`, `cases` |
| 5 | Every distribution is a coin (Lean only) | `eq_coin` | `apply`, `chance`, `chance_eq` |
| 6 | Always true | `coin_const` | `coin_total`, `pure_true` |
| 7 | Surely false | `map_pure`, `rfl` | `rfl`, `map_pure` |
| 8 | From sides to numbers | `congr`, `funext`, `cases b <;> rfl` | `congr`, `funext`, `<;>` |
| 9 | Surely zero | | |
| 10 | Boss: flipping a coin | `coin_not` | |

## World 2 — Draw, then Compute (Lean leads; boards stay as they are)

Monad laws as rules, do-notation explained. The order is already right; the texts get a short
explanation of `do`, `←` and `>>=` (Lean's way of writing "throw, then …").

## World 3 — Building with Coins (now as circuits)

Same levels, proofs and lemmas as before, but the board is a circuit with several coins (as world ∧
with coins): inputs `x ← coin p`, `y ← coin p`, …, gates and/or/not/toNat/plus, the output box with
histogram, the bars and *Throw 100 times* beside it. The levels about `binom p n` (`binom_succ'`,
`binom_add`) start with the part that is `B(2, p)` already wired (`start`), so that the player adds
what the statement adds.

## World 4 — Coins that wait (bind; new, replaces "Circuits with Coins")

The old world 4 was world 3 again as circuits; that is now world 3. The new world 4 is bind for
coins: a coin thrown *after* another, **which** coin depending on a wire (the input `y` has a port on
its side: `y ← bif c then coin q else coin r`). The bind gate of world ∧, now with distributions in
its fields. The targets get more complex: trying again, copying, waiting for heads, three tries.

Lean: a new rule `bind_true : (μ >>= f) true = μ true * f true true + μ false * f false true` (the
mass of a bind at `true`: through `true` and through `false`), with `Bool.cond_true/false`,
`coin_true/false`, `pure_true`, `pure_bind`, `mul_one`, `mul_zero`, `add_zero`. Statements are masses
at `true` (the board shows the whole distribution; `bool_ext` says that this suffices).

## Phones

Hover does not exist there: a long press on an inventory chip shows its statement; a switch
*Show statements* shows the statements of all chips (on every screen).

## Checks

- every solution only uses what came before (script), every new statement checked in Lean;
- every level played in the browser with the mouse: board, then proof (`tests/playthrough.mjs`).
