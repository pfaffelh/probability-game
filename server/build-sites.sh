#!/usr/bin/env bash
# Builds the site of each branch into <sites>/<branch> (`show`, `main`, `monad`, or those given), each
# from its own git worktree, and writes <sites>/allowed.txt: the Lean contexts of all branches, for
# the bridge (`ALLOWED`). A branch checked out somewhere already is built there; else a worktree is
# made in <repo>/../probability-game-branches/<branch>, at the newest commit of origin/<branch>.
# The worktrees share the Lean packages (Verso) of this checkout.
# Usage: server/build-sites.sh <sites> [branch …]
set -euo pipefail
sites=$(realpath -m "$1"); shift
branches=("$@")
[ ${#branches[@]} -eq 0 ] && branches=(show main monad)
repo=$(cd "$(dirname "$0")/.." && pwd)
trees=$(realpath -m "$repo/../probability-game-branches")
mkdir -p "$sites"
git -C "$repo" fetch -q origin
: > "$sites/allowed.txt.new"
for b in "${branches[@]}"; do
  dir=$(git -C "$repo" worktree list --porcelain | awk -v b="refs/heads/$b" '/^worktree /{w=substr($0,10)} $0=="branch "b{print w}')
  if [ -z "$dir" ]; then
    dir=$trees/$b
    git -C "$repo" worktree add -q "$dir" "$b" 2>/dev/null || git -C "$repo" worktree add -q -b "$b" "$dir" "origin/$b"
  fi
  if [ "$dir" != "$repo" ]; then
    git -C "$dir" merge -q --ff-only "origin/$b" 2>/dev/null || true
    mkdir -p "$dir/.lake" && [ -e "$dir/.lake/packages" ] || ln -s "$repo/.lake/packages" "$dir/.lake/packages"
  fi
  echo "== $b ($dir, $(git -C "$dir" log -1 --format='%h %s' | cut -c1-60))"
  (cd "$dir" && lake build > "$sites/build-$b.log" 2>&1) || { grep -E '^error' "$sites/build-$b.log" | head -20; exit 1; }
  # (Verso does not empty its output: without this, pages of worlds that are gone would stay online)
  rm -rf "$dir/_out/html-multi"
  (cd "$dir" && lake exe probgame > /dev/null)
  rm -rf "$sites/$b.new" && cp -r "$dir/_out/html-multi" "$sites/$b.new"
  rm -rf "$sites/$b.old" && { [ -d "$sites/$b" ] && mv "$sites/$b" "$sites/$b.old" || true; } && mv "$sites/$b.new" "$sites/$b" && rm -rf "$sites/$b.old"
  (cd "$dir" && sha256sum Lean/Rules.lean Lean/World*.lean) >> "$sites/allowed.txt.new"
done
sort -u -k1,1 "$sites/allowed.txt.new" > "$sites/allowed.txt" && rm "$sites/allowed.txt.new"
echo "built: ${branches[*]} into $sites"
