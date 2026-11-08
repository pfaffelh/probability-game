#!/usr/bin/env bash
# While working: builds this checkout only, puts the site into <sites>/<branch> (served, e.g., by
# `python3 -m http.server 8004 --directory <sites>`), and plays one world (or all) on a desktop.
# The full check before a deploy is server/build-sites.sh and all of tests/ (see README).
# Usage: tests/dev.sh <sites> [page]      e.g. tests/dev.sh ~/sites One-Coin
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
sites=$(realpath -m "$1"); page=${2:-}
branch=$(git -C "$here" branch --show-current)
cd "$here"
lake build 2>&1 | grep -E '^error' && exit 1 || true
lake exe probgame > /dev/null
rm -rf "$sites/$branch.new" && cp -r _out/html-multi "$sites/$branch.new" && rm -rf "$sites/$branch" && mv "$sites/$branch.new" "$sites/$branch"
./check-proofs.sh > /dev/null && echo "solutions: checked"
BASE="http://127.0.0.1:8004/$branch/" ONLY="$page" node tests/play.mjs desktop | grep -E 'FAIL|failures|level'
