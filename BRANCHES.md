# The branches: three editions of the game

| Branch | Edition | What | Online |
|---|---|---|---|
| `main` | `main` | The game in development: chance, with what it needs. *True and False* (the tutorial), *One Coin* (what a distribution on `Bool` is: `bool_ext`, `coin_not`), *Draw, then Compute* (`do` blocks and the monad laws for `DiscreteMeasure`), *Building with Coins* (circuits of coins and `B(n, p)`). Each level: the board, then the proof. | `/main/` |
| `monad` | `main` | `main` and the other monads: *Walking on the Grid* (`Id`, `Set`). Only here. | `/monad/` |
| `show` | `show` | The boards alone, without Lean and without proofs: a graphical target, the building blocks (coins, `B(n, p)`), and composing them (moves, circuits). *One Coin*, *Building with Coins*. | `/show/` |

## How the branches differ

The engine is the same on every branch: `ProbGame/game.js`, `ProbGame/game.css`,
`ProbGame/Level.lean`, `Main.lean`, `server/`, `tests/*.mjs`, `tests/proofs.py`, `check-proofs.sh`.
A branch differs from `main` only in

* `ProbGame.lean`: the edition (`def ProbGame.edition`), the worlds it includes, and the front
  page (each edition ends with the lexicon, `{include 1 ProbGame.Lexicon}`);
* the files of the worlds it adds (on `monad`).

A world is a set of files with the same name `W`:

| File | What |
|---|---|
| `ProbGame/Worlds/W.lean` | the levels: boards, texts in English and German, statements, what each brings into the inventory, the moves and the proof that solve it |
| `Lean/WorldW.lean` | its Lean context, if it has one of its own (else `Lean/WorldCoin.lean` for the boards and `Lean/Rules.lean` for the proofs) |

A part of a world that suits one edition only, e.g. a level whose board is only interesting with its
proof, is put into `:::::only (edition := "main")` (or `"show"`); every branch has the world, and
`game.js` removes the parts of the other edition before it counts the levels (the tests know it from
the source). (The edition `monad` is `main`.)

The tests take the worlds from the site they test (its table of contents), so no list of worlds
needs to be kept anywhere else. In the edition `show`, `game.js` shows no Lean and creates no
proofs, and `:::proofen`/`:::proofde` blocks are hidden everywhere (also on the front page and in the
introductions of worlds: text about proofs goes there).

## How changes flow

Everything common is done on `main`, and `main` is merged into the other branches:

```bash
git switch monad && git merge main && git push
git switch show && git merge main && git push
```

Conflicts can only come up in `ProbGame.lean` (when `main` changes its front page or its worlds).
`monad` and `show` are never merged into `main`. A fix made on another branch that belongs to
everyone (in the engine, or in a world that `main` has) is brought over with
`git cherry-pick <commit>` on `main`; for that, such a commit should touch nothing else.

Levels have no numbers: each says what it brings (`new`), and its inventory is what the levels of its
group before it brought (see README). *True and False* and *Walking on the Grid* each have an
inventory of their own; the worlds of chance share one. A level, or a world, can therefore be added,
moved or removed on one branch without touching anything else.

## Building and serving

`server/build-sites.sh <sites>` builds every branch in a worktree of its own and writes the sites to
`<sites>/show`, `<sites>/main`, `<sites>/monad`, with `<sites>/allowed.txt`, the Lean contexts of all
branches for the bridge. One bridge serves all editions. On the server, `server/deploy.sh` does
this, and nginx serves `<sites>/<branch>` at `/<branch>/`; `/` leads to `/main/`.
