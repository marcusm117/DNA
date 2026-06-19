#!/usr/bin/env bash
# Phase C, one command (the HUMAN runs this — see FAITHFUL.md "Phase C — wire + verify").
#
# After Phase B's gate B passes (`check_step.py <propdir> --all` exits 0), Phase C is four mechanical
# steps that each want a DIFFERENT argument shape (the slash-vs-dot footgun). This wrapper takes ONE
# propdir and runs them in order, STOPPING at the first failure (so you never wire-then-skip a check):
#   1. wire_main.py <propdir>              — commit the wiring, strip 30s caps, build Main once
#   2. check_faithful.sh <module>          — text (crit 1) + deps (crit 3), book-aware (needs the build)
#   3. check_steps.py <propdir>/Main.lean  — claim types unchanged since gate A
#   4. check_signatures.py                 — no proposition statement was altered
# All four green ⟹ the prop is faithful (gate C).
#
# Usage (run from anywhere in the repo — paths resolve to LeanEuclidPlus/):
#   scripts/phase_c.sh Book2/Prop04            # the four steps, stop on first failure
#   scripts/phase_c.sh Book2/Prop04/Main.lean  # same (Main.lean suffix tolerated)
#   scripts/phase_c.sh Book2/Prop04 --unwire   # reverse wiring back to the Phase-B all-sorry state
#
# Exit code: 0 iff every step passed (or --unwire succeeded); otherwise the failing step's code.

set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"   # LeanEuclidPlus/
cd "$HERE"

if [ "$#" -lt 1 ] || [ "$#" -gt 2 ]; then
  echo "usage: scripts/phase_c.sh <propdir> [--unwire]   (e.g. Book2/Prop04)" >&2
  exit 2
fi

# Normalize the input to a propdir like "Book2/Prop04": strip a trailing /Main.lean, a trailing slash,
# and accept a dotted module form (Book2.Prop04) too.
RAW="$1"
RAW="${RAW%/Main.lean}"
RAW="${RAW%/}"
PROPDIR="${RAW//./\/}"                 # Book2.Prop04 -> Book2/Prop04 (harmless if already a path)
MODULE="${PROPDIR//\//.}.Main"         # Book2/Prop04 -> Book2.Prop04.Main (sentences live in the .Main submodule post-relocation)
MAIN="$PROPDIR/Main.lean"

if [ ! -f "$MAIN" ]; then
  echo "phase_c: no $MAIN under $HERE — is the propdir right? (e.g. Book2/Prop04)" >&2
  exit 2
fi

# --unwire: just reverse the wiring and stop (no checks — you're going back to Phase B).
if [ "$#" -eq 2 ]; then
  if [ "$2" != "--unwire" ]; then
    echo "phase_c: unknown second arg '$2' (only --unwire)" >&2
    exit 2
  fi
  echo "=== phase_c $PROPDIR: --unwire (revert to Phase-B all-sorry state) ==="
  exec python3 scripts/wire_main.py "$PROPDIR" --unwire
fi

# Run a labelled step; on non-zero exit, announce which step failed and abort the whole sequence.
step=0
run_step() {
  step=$((step + 1))
  local label="$1"; shift
  echo
  echo "=== phase_c [$step/4] $label ==="
  echo "    \$ $*"
  "$@"
  local rc=$?
  if [ "$rc" -ne 0 ]; then
    echo
    echo "✗ phase_c STOPPED at step $step ($label) — exit $rc. Fix it, then re-run scripts/phase_c.sh $PROPDIR." >&2
    echo "  (If step 1 wired but a later check failed, the fix is in a backing file: " >&2
    echo "   scripts/phase_c.sh $PROPDIR --unwire  returns Main to Phase B.)" >&2
    exit "$rc"
  fi
}

echo "### Phase C for $PROPDIR  (module $MODULE) — stops at first failure"
run_step "wire Main + build once"        python3 scripts/wire_main.py "$PROPDIR"
run_step "faithfulness (text + deps)"    scripts/check_faithful.sh "$MODULE"
run_step "claim types unchanged"         python3 scripts/check_steps.py "$MAIN"
run_step "proposition statements intact" python3 scripts/check_signatures.py

echo
echo "✓ phase_c: all 4 steps passed — $PROPDIR is FAITHFUL (gate C)."
