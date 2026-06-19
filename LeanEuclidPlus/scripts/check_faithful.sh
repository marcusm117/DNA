#!/usr/bin/env bash
# Convenience wrapper: extract faithfulness data from a BUILT module's .olean and check it.
# Combines the two fast, no-z3 steps (extract + check). It does NOT build — run `lake build <mod>`
# yourself first (incremental; the .olean must be up to date or you check stale data).
#
# Usage:
#     scripts/check_faithful.sh Book2                       # check every proposition in Book2
#     scripts/check_faithful.sh Book2.Prop01.Main           # one prop (its sentences live in the .Main submodule)
#     scripts/check_faithful.sh Book2 --keep book2.json     # also save the extracted JSON to inspect
#
# For a quick pre-build sanity check of a single source file (number-only deps, not book-aware), use
# the Python checker directly instead:  python3 scripts/check_faithful.py "Book2/Prop01/Main.lean"
set -euo pipefail

MOD="${1:?usage: check_faithful.sh <RootModule> [--keep <path>]   (e.g. Book2)}"
KEEP=""
if [[ "${2:-}" == "--keep" ]]; then
  KEEP="${3:?--keep requires a path, e.g. --keep book2.json}"
fi

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"   # LeanEuclidPlus/
cd "$HERE"

if [[ -n "$KEEP" ]]; then
  JSON="$KEEP"                       # persistent: written where you asked, not deleted
else
  JSON="$(mktemp -t faithful-XXXXXX.json)"
  trap 'rm -f "$JSON"' EXIT          # temp: cleaned up on exit
fi

lake exe faithful_export "$MOD" > "$JSON"
# Capture the checker's exit code: it is the meaningful PASS(0)/FAIL(1) result the caller branches on.
# (`set -e` is disabled around it so a FAIL doesn't abort before we can print the --keep note, and so
# the script's final exit code is the checker's, not that of the trailing `[[ ]]` test.)
set +e
python3 scripts/check_faithful.py --olean "$JSON"
rc=$?
set -e
[[ -n "$KEEP" ]] && echo "  (extracted JSON kept at: $KEEP)"
exit "$rc"
