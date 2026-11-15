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

The Lean statement of a circuit level is now **your circuit = the target table**, written as a
decision input after input: `(x && y) = (bif x then (bif y then true else false) else (bif y then
false else false))`. The table on the board and the right side in Lean are the same thing. No more
`x && y = x && y`. (First planned as `fun | false, false => … | …`: Lean accepts it, but the proof
states of the game's Lean server do not know the auxiliary definition that `fun | …` makes, so every
tactic failed with "unknown name". `bif` has no such definition.)

| # | level | board | Lean | new |
|---|---|---|---|---|
| 1 | A wire | x → output | `x = x`, `rfl` | `rfl` (equality) |
| 2 | Not true | true → not | `(!true) = false`, `rfl` | `rfl` reduces |
| 3 | Flipped twice | one not given | `!(!x) = x`: `cases x`, `rfl`, `rfl` | `cases`, lemma `Bool.not_not` |
| 4 | Always true, without always true | x twice | `cases x <;> rfl` | `<;>` |
| 5 | Both (and) | two inputs | `cases x <;> cases y <;> rfl` | |
| 6 | Exactly one (xor) | two inputs | `decide +revert` | `decide` |
| 9–11 | bind (and, xor, if-then) | the bind gate | table again | |
| 12–13 | the map f | f given | `rw [h, h]`; `decide +revert` | `rw` |
| 14–16 | numbers, count, majority | toNat, plus | table with numbers | |

(4 and 5 swap: `<;>` comes with one input, then is needed with two.)
Lean texts added: how to read a statement (`example`, hypotheses, `:`, the goal after `⊢`, a tactic),
how the table reads as `bif`.

Later, not yet (the user's wish): Lean-only levels `x = true ∨ x = false` and the four maps
`Bool → Bool` at the end of this world.

## World 1 — One Coin (one coin, top to bottom; Lean grows)

All boards top to bottom as in world ∧: the coin `x ← coin p` above, gates, the output box below
with a small histogram (target dashed, output filled) and the masses `p`, `1 - p`. New gates:
*always T*, *always F* (the constant maps; `heads`/`tails` of the old bars).

| # | level | Lean | new |
|---|---|---|---|
| 1 | Where does the mass go? (not) | mass at true (no lemma: the boss needs the computation again) | `rw`, `map_true`, `coin_true`, … |
| 2 | The rest of the mass (Lean only) | `mass_not μ b : μ b = 1 - μ (!b)` | `cases`, `mass_total`, `mass_ne_top`, `ENNReal.add_sub_cancel_left`, `add_comm`, `exact` |
| 3 | One bar is enough (Lean only) | `bool_ext` | `ext` |
| 4 | Every distribution is a coin (Lean only) | `eq_coin` | `apply`, `chance`, `chance_eq` |
| 5 | Always true | `coin_const` | `coin_total`, `pure_true` |
| 6 | Surely false | `map_pure`, `rfl` | `rfl`, `map_pure` |
| 7 | From sides to numbers | `congr`, `funext`, `cases b <;> rfl` | `congr`, `funext`, `<;>` |
| 8 | Surely zero | | |
| 9 | Boss: flipping a coin | `coin_not`: `bool_ext` and the computation of level 1 (5 lines) | |

## (World 2 — Draw, then Compute: dissolved on 2026-11-14 into world 3, see below)

Monad laws as rules, do-notation explained (`do`, `←`, `>>=`, `fun x => …`). The boards are one-coin
circuits too (as world 1); where the statement has a fixed number of `not`, the first ones are given.
The boss ends at `coin (σ p)` and needs the boss of world 1, `coin_not`.

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

## Done on 2026-11-14 (night)

All of the above is built. Checked: every solution in Lean (worlds ∧ to 4); the order of
introduction by script (nothing used before it comes); every level played in the browser with the
mouse, desktop for all worlds, phone size for ∧, 3 and 4, and the edition `show` (boards only).
Bosses: ∧ the majority (hardest board), 1 `coin_not` (5 lines, all of the world), 2 three flips (with
`coin_not`), 3 the majority (9 lines), 4 three tries.

Open: the Lean-only levels of world ∧ (`x = true ∨ x = false`, the four maps), `focus` per level,
the monad branch (still the old worlds).

## 2026-11-14 evening: Draw, then Compute dissolved

Its boards repeated earlier ones (not, a wire, two nots, always T). Its rules now come in
*Building with Coins* where first needed: `simp only`, `bind_map_left` (level 2), `bind_assoc`,
`pure_bind` (level 7, `binom p 2`), `bind_pure` (`binom_add`); the do/←/>>= text is in its intro.
`map_eq_pure_bind` is gone (nothing needed it). Worlds now: ∧, 1 One Coin, 2 Building with Coins,
3 Coins that Wait.

Circuits, 2026-11-14 evening (user): levels Both, Or without or (De Morgan), The same removed (trivial); then toNat levels out, f-levels out into a new world *Maps* (after One Coin: f (f (f b)) = f b, lemma Bool.apply_apply_apply; and f <$> f <$> f <$> coin p = f <$> coin p with map_map), the three bind levels moved to the start of *Coins that Wait* as deterministic training. Circuits: 6 levels. rw now comes in One Coin 1.

Then (user): the majority out; Exactly one (xor) is the boss of Circuits (cases x <;> cases y <;> rfl): Circuits = 5 levels; `decide` comes in Maps 1. The button "Show the values row by row" is gone: tap a table row or a column of the output box.

norm_num (user, 2026-11-14): in the inventory from Building with Coins 1 on; coin_true, coin_false, pure_true are simp in Lean/Rules.lean, so after the structural rule (rw [bind_true]) a bare `norm_num` computes. Bare norm_num solves no level (checked).

## 2026-11-15: Counting, a world of its own; Coins that Wait a side way

(User.) Everything with `toNat` is in the new world *Counting* (4): from One Coin *From sides to
numbers* and *Surely zero*, from Building with Coins the levels from *The number of `true`* to the
majority (boss). Building with Coins keeps and/or/not; its boss is now *Exactly one `true`*. `congr`
and `funext` come in Maps 2 (they were in the toNat level of One Coin). Counting and Coins that Wait
both come after Building with Coins and do not need each other: the map draws the fork (`SIDE_WAYS` in
game.js), and Counting's levels have `(route := "count")`, the inventory group `chance.count`, so that
Coins that Wait (group `chance`, after it in the document) does not get Counting's rules.

Also on 2026-11-15: the proof as in the NNG4 (each line with the goal after it, ✕ per line), the board
zooms on phones and uses the whole width of the screen there.

## 2026-11-15: world *Masses* (μ) between Circuits and One Coin

(User.) One Coin 1 brought nine rules at once. Now a world of seven Lean-only levels before it, one
per rule that One Coin needs, the definitional ones proved by `rfl` (and then lemmas of the player):
`coin_true`, `coin_false`, `Bool.not_false`, `Bool.cond_true`, `Bool.cond_false`; `Bool.not_true` is
the lemma of Circuits 2 (`(!true) = false`, `rfl`). The given rules get a level that uses them once:
`zero_add` (with `rw`), `map_true`. Its intro says what `DiscreteMeasure`, `coin p`, `μ x`, `f <$> μ`
are. Map sign μ (no number, so One Coin stays 1).
