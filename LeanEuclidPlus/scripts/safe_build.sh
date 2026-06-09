#!/bin/bash
# Serialized `lake build` for parallel per-proposition work.
# Many AIs edit different Book2/PropNN.lean files concurrently; they all
# build through this wrapper so only ONE `lake build` runs at a time.
# That keeps .lake/build/ and Lake's trace DB from being corrupted by
# concurrent writers.
#
# Usage:  scripts/safe_build.sh Book2.Prop07
#         scripts/safe_build.sh Book2.Prop07 Book2.Prop08   # multiple targets ok
#
# Exit code is lake's exit code, so callers can branch on success/failure.

set -euo pipefail

# `euclid_finish` shells out to the SMT solvers `z3` and `cvc5` BY BARE NAME, so they must be on
# PATH or every proof build fails with `FileNotFoundError: 'z3'`. They live only in the project
# venv (~/.venvs/leaneuclid/bin). Put that bin on PATH here so callers never need to `source` it
# (and so it works even when each shell invocation is fresh). Override with LEANEUCLID_VENV.
VENV="${LEANEUCLID_VENV:-$HOME/.venvs/leaneuclid}"
if [ -d "$VENV/bin" ]; then
  export PATH="$VENV/bin:$PATH"
fi

# Resolve repo root (this script lives in <root>/scripts/).
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LOCK="$ROOT/.lake/build.lock"

mkdir -p "$ROOT/.lake"

if [ "$#" -eq 0 ]; then
  echo "usage: $0 <Lean.Target> [more targets...]" >&2
  exit 2
fi

# flock holds an exclusive lock on FD 9 for the duration of the lake build.
# Other invocations block here until the running build releases the lock.
exec 9>"$LOCK"
echo "[safe_build] waiting for build lock..." >&2
flock 9
echo "[safe_build] lock acquired, building: $*" >&2

cd "$ROOT"
lake build "$@"
