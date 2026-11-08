#!/bin/sh
# Checks the Lean side of the game against Mathlib and the journal's DiscreteMeasure:
# * Proofs/*.lean: the statements of the levels with Mathlib's PMF;
# * Lean/Rules.lean and Lean/World*.lean: the contexts (the rules of the proofs and of the boards);
# * the solutions of the levels (`:::solution` in ProbGame/Worlds/*.lean), as a player types them,
#   each in the rules of its level;
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
# the solutions of the levels (`:::solution`, read by tests/levels.py), each world in the rules of
# its levels, as a player types them
python3 -I "$here/tests/levels.py" > "$tmp/levels.json"
python3 -I - "$tmp" "$here" <<'PY'
import json, sys
from pathlib import Path
tmp, here = Path(sys.argv[1]), Path(sys.argv[2])
files = {}
for world, levels in json.loads((tmp / 'levels.json').read_text()).items():
    for l in levels:
        if l['proof']:
            key = (world.split('.')[-1], l['context'])
            body = '\n'.join('  ' + x for x in l['solution']) or '  sorry'
            files.setdefault(key, []).append(f"example {l['proof']} := by\n{body}\n")
for (world, context), exs in files.items():
    name = f"Solutions{world}-{Path(context).stem}.lean"
    (tmp / name).write_text('import Journal.Notes.DiscreteMeasure.Thinning\n' + (here / context).read_text() + '\n' + '\n'.join(exs))
PY
for f in "$tmp"/Solutions*.lean; do
  echo "checking the solutions $(basename "$f")"
  out=$(lake env lean "$f" 2>&1) || { echo "$out"; exit 1; }
  if echo "$out" | grep -q "declaration uses 'sorry'"; then echo "$out"; echo "a level without a solution"; exit 1; fi
done
rm -r "$tmp"
echo "all checked"
