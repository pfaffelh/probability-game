#!/usr/bin/env bash
# On the server (without root): fetch, build and restart the game. Everything lives in ~/lean:
#   journal/            the journal (DiscreteMeasure), branch master, with Mathlib from the cache
#   repl/               leanprover-community/repl, built with the journal's toolchain
#   probability-game/   this repository, branch main (the bridge runs from here)
#   probability-game-branches/<branch>   worktrees of the other branches (show, monad)
#   sites/<branch>      the built sites, served at /<branch>/ (server/build-sites.sh)
#   nginx/              nginx's prefix: `sites` links ~/lean/sites
#   allowed.txt         the contexts the bridge accepts (Lean/Rules.lean, Lean/World*.lean of all branches)
# The first time: clone the three repositories into ~/lean (see server/README.md).
set -euo pipefail
L=$HOME/lean
export PATH=$HOME/bin:$HOME/.elan/bin:$PATH
# the C files of Verso's Markdown package want `cc`; without a system compiler, the toolchain's clang
if ! command -v cc >/dev/null; then
  mkdir -p ~/bin && ln -sf "$(ls -d ~/.elan/toolchains/*/bin/clang | head -1)" ~/bin/cc
fi

git -C $L/probability-game pull -q --ff-only
git -C $L/journal pull -q --ff-only
(cd $L/journal && lake exe cache get >/dev/null && lake build Journal.Notes.DiscreteMeasure.Thinning)
cp $L/journal/lean-toolchain $L/repl/lean-toolchain && (cd $L/repl && lake build)
$L/probability-game/server/build-sites.sh $L/sites show main monad
cp $L/sites/allowed.txt $L/allowed.txt
mkdir -p $L/nginx/tmp && ln -sfn $L/sites $L/nginx/sites

mkdir -p ~/.config/systemd/user && cp $L/probability-game/server/systemd/*.service ~/.config/systemd/user/
systemctl --user daemon-reload
if [ "${1:-}" = --start ]; then
  systemctl --user enable probgame-bridge probgame-web
  systemctl --user restart probgame-bridge probgame-web
elif systemctl --user -q is-active probgame-bridge; then
  systemctl --user restart probgame-bridge
  systemctl --user reload probgame-web
fi
systemctl --user --no-pager status probgame-bridge probgame-web | grep -E '●|Active' || true
