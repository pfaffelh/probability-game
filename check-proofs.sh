#!/bin/sh
# Checks the Lean side of the game against Mathlib and the journal's DiscreteMeasure:
# * Proofs/*.lean: the statements of the levels with Mathlib's PMF;
# * Lean/*.lean: the rules of the worlds (the context in which the game normalises its state), with
#   `import Journal.Notes.DiscreteMeasure.Thinning` in front, as the bridge loads them.
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
for f in "$here"/Lean/*.lean; do
  echo "checking the rules $(basename "$f")"
  { echo "import Journal.Notes.DiscreteMeasure.Thinning"; cat "$f"; } > "$tmp/$(basename "$f")"
  lake env lean "$tmp/$(basename "$f")"
done
rm -r "$tmp"
echo "all checked"
