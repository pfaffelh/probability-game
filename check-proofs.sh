#!/bin/sh
# Checks the Lean statements of the levels (Proofs/*.lean) against Mathlib: runs `lake env lean` in a
# project that has Mathlib built. Usage: ./check-proofs.sh [mathlib project]   (default ~/Code/lean/journal)
set -e
here=$(cd "$(dirname "$0")" && pwd)
project=${1:-$HOME/Code/lean/journal}
cd "$project"
for f in "$here"/Proofs/*.lean; do
  echo "checking $(basename "$f") with $(cat lean-toolchain)"
  lake env lean "$f"
done
echo "all proofs checked"
