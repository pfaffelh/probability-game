#!/bin/sh
# Checks the Lean side of the game against Mathlib and the journal's DiscreteMeasure:
# * Proofs/*.lean: the statements of the levels with Mathlib's PMF;
# * Lean/Rules.lean and Lean/World*.lean: the contexts (the rules of the proofs and of the boards);
# * for each world (tests/worlds/<World>.json), its solutions Lean/Solutions<World>.lean, the proofs of
#   its levels as a player types them, in its context;
# each with `import Journal.Notes.DiscreteMeasure.Thinning` in front, as the bridge loads them.
# Usage: ./check-proofs.sh [journal]   (default ~/Code/lean/journal)
set -e
here=$(cd "$(dirname "$0")" && pwd)
project=${1:-$HOME/Code/lean/journal}
cd "$project"
for f in "$here"/Proofs/*.lean; do
  echo "checking $(basename "$f") with $(cat lean-toolchain)"
  lake env lean "$f"
done
tmp=$(mktemp -d)
for f in "$here"/Lean/Rules.lean "$here"/Lean/World*.lean; do
  echo "checking the rules $(basename "$f")"
  { echo "import Journal.Notes.DiscreteMeasure.Thinning"; cat "$f"; } > "$tmp/$(basename "$f")"
  lake env lean "$tmp/$(basename "$f")"
done
for w in "$here"/tests/worlds/*.json; do
  set -- $(python3 -I -c 'import json, sys; w = json.load(open(sys.argv[1])); print(w["solutions"], w["context"])' "$w")
  echo "checking the solutions $1 in $2"
  { echo "import Journal.Notes.DiscreteMeasure.Thinning"; cat "$here/Lean/$2" "$here/Lean/$1"; } > "$tmp/$1"
  lake env lean "$tmp/$1"
done
rm -r "$tmp"
echo "all checked"
