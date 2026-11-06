#!/bin/sh
# Checks the Lean side of the game against Mathlib and the journal's DiscreteMeasure:
# * Proofs/*.lean: the statements of the levels with Mathlib's PMF;
# * Lean/Rules.lean, Lean/World0.lean, Lean/World1.lean: the rules of the proofs and of worlds 0
#   and 1 (the contexts), and Lean/Solutions.lean, Lean/Solutions0.lean, the proofs of the levels as
#   a player types them, with
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
for f in "$here"/Lean/Rules.lean "$here"/Lean/World0.lean "$here"/Lean/World1.lean; do
  echo "checking the rules $(basename "$f")"
  { echo "import Journal.Notes.DiscreteMeasure.Thinning"; cat "$f"; } > "$tmp/$(basename "$f")"
  lake env lean "$tmp/$(basename "$f")"
done
echo "checking the solutions Solutions.lean"
{ echo "import Journal.Notes.DiscreteMeasure.Thinning"; cat "$here/Lean/Rules.lean" "$here/Lean/Solutions.lean"; } > "$tmp/Solutions.lean"
lake env lean "$tmp/Solutions.lean"
echo "checking the solutions Solutions0.lean"
{ echo "import Journal.Notes.DiscreteMeasure.Thinning"; cat "$here/Lean/World0.lean" "$here/Lean/Solutions0.lean"; } > "$tmp/Solutions0.lean"
lake env lean "$tmp/Solutions0.lean"
rm -r "$tmp"
echo "all checked"
