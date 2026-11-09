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

git -C $L/probability-game pull -q --ff-only

# The C files of Verso's Markdown package (MD4Lean) are compiled with `cc` (only compiled: Lean links
# with its own toolchain); they need the C headers of the system (libc6-dev). Without a C compiler on
# the system, `cc` is the clang of the Lean toolchain, with clang's own headers from the toolchain.
rm -rf $L/sysroot  # (the C headers were unpacked there while the system had none)
if [ -x /usr/bin/cc ]; then
  rm -f ~/bin/cc
else
  T=$(cd $L/probability-game && lean --print-prefix)
  mkdir -p ~/bin && rm -f ~/bin/cc
  cat > ~/bin/cc <<EOF
#!/bin/sh
# made by server/deploy.sh: the clang of the Lean toolchain, with its headers and those of the system
exec $T/bin/clang -isystem $T/include/clang "\$@"
EOF
  chmod +x ~/bin/cc
fi

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
