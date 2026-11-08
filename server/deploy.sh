#!/usr/bin/env bash
# On the server (without root): fetch, build and restart the game. Everything lives in ~/lean:
#   journal/            the journal (DiscreteMeasure), branch master, with Mathlib from the cache
#   repl/               leanprover-community/repl, built with the journal's toolchain
#   probability-game/   this repository, branch main (the bridge runs from here)
#   probability-game-branches/<branch>   worktrees of the other branches (show, monad)
#   sites/<branch>      the built sites, served at /<branch>/ (server/build-sites.sh)
#   nginx/              nginx's prefix: `sites` links ~/lean/sites
#   allowed.txt         the contexts the bridge accepts (Lean/Rules.lean, Lean/World*.lean of all branches)
#   sysroot/            the C headers of glibc and Linux, when the system has none (see below)
# The first time: clone the three repositories into ~/lean (see server/README.md).
set -euo pipefail
L=$HOME/lean
export PATH=$HOME/bin:$HOME/.elan/bin:$PATH

git -C $L/probability-game pull -q --ff-only

# The C files of Verso's Markdown package (MD4Lean) are compiled with `cc` (only compiled: Lean links
# with its own toolchain). Without a C compiler and C headers on the system (no libc6-dev, no root),
# `cc` is the clang of the Lean toolchain, with clang's headers from the toolchain and those of glibc
# and Linux unpacked from Ubuntu's packages into ~/lean/sysroot: libc6-dev in the version of the
# installed glibc (fetched again when glibc is updated) and linux-libc-dev.
if [ -e /usr/include/stdio.h ] && [ -x /usr/bin/cc ]; then
  rm -f ~/bin/cc
else
  T=$(cd $L/probability-game && lean --print-prefix)
  S=$L/sysroot
  v=$(dpkg-query -W -f='${Version}' libc6)
  if [ "$(cat $S/version 2>/dev/null)" != "$v" ]; then
    rm -rf $S && mkdir -p $S/debs
    (cd $S/debs && apt-get download -q "libc6-dev=$v" linux-libc-dev >/dev/null)
    for d in $S/debs/*.deb; do dpkg -x "$d" $S; done
    echo "$v" > $S/version
  fi
  mkdir -p ~/bin && rm -f ~/bin/cc
  cat > ~/bin/cc <<EOF
#!/bin/sh
# made by server/deploy.sh: the clang of the Lean toolchain, with the C headers of ~/lean/sysroot
exec $T/bin/clang -isystem $T/include/clang -isystem $S/usr/include/x86_64-linux-gnu -isystem $S/usr/include "\$@"
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
