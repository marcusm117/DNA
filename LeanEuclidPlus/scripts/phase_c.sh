#!/usr/bin/env bash
# Phase C wrapper (the HUMAN runs this — see FAITHFUL.md "Phase C — wire + verify").
#
# SINGLE-PROP (verbose, stops at first failure within the prop):
#   scripts/phase_c.sh Book3/Prop04
#   scripts/phase_c.sh Book3/Prop04/Main.lean   # Main.lean suffix tolerated
#   scripts/phase_c.sh Book3.Prop04.Main         # dotted module form tolerated
#   scripts/phase_c.sh Book3/Prop04 --unwire     # reverse wiring back to Phase-B
#
# MULTI-PROP (quiet — prints ONLY failures + a one-line summary; nothing per passing prop):
#   scripts/phase_c.sh Book3                     # all Prop* in Book3
#   scripts/phase_c.sh Book3 all                 # same
#   scripts/phase_c.sh Book3 4 5 6               # specific props (zero-pad optional)
#   scripts/phase_c.sh Book3 11-16               # a range, props 11..16
#   scripts/phase_c.sh Book3 11-                 # prop 11 to the end of the book
#   scripts/phase_c.sh Book3 1 10-14 20          # mix singles + ranges
#   scripts/phase_c.sh Book3 1,10,2              # commas tolerated
# (out-of-range / missing numbers are silently skipped; `Prop` prefix optional on any number)
#
# Exit code: 0 iff all selected props passed; non-zero on any failure.

set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"   # LeanEuclidPlus/
cd "$HERE"
source "$HERE/scripts/prop_select.sh"                     # shared BOOK/range selector grammar

[ "$#" -lt 1 ] && { echo "usage: scripts/phase_c.sh <propdir|book> [props…|all|N-M|N-] [--unwire]" >&2; exit 2; }

# ── detect mode ───────────────────────────────────────────────────────────────
# Single-prop: first arg contains "/" or "Prop" (path or dotted-module form).
# Multi-prop: first arg is a bare book dir like "Book3".

if [[ "$1" == *"/"* ]] || [[ "$1" =~ [Pp]rop ]]; then

# ═════════════════════════════════════════════════════════════════════════════
# SINGLE-PROP MODE (verbose)
# ═════════════════════════════════════════════════════════════════════════════

  [ "$#" -gt 2 ] && { echo "phase_c: too many args for single-prop mode" >&2; exit 2; }

  RAW="$1"; RAW="${RAW%/Main.lean}"; RAW="${RAW%/}"
  PROPDIR="${RAW//./\/}"
  MODULE="${PROPDIR//\//.}.Main"
  MAIN="$PROPDIR/Main.lean"

  [ ! -f "$MAIN" ] && { echo "phase_c: no $MAIN under $HERE" >&2; exit 2; }

  if [ "${2:-}" = "--unwire" ]; then
    echo "=== phase_c $PROPDIR: --unwire (revert to Phase-B all-sorry state) ==="
    exec python3 scripts/wire_main.py "$PROPDIR" --unwire
  fi

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
      echo "  (If step 1 wired but a later check failed: scripts/phase_c.sh $PROPDIR --unwire)" >&2
      exit "$rc"
    fi
  }

  echo "### Phase C for $PROPDIR  (module $MODULE) — stops at first failure"
  if grep -rl "systemE.solverTime 30" "$PROPDIR" 2>/dev/null | grep -q .; then
    run_step "wire Main + build once"      python3 scripts/wire_main.py "$PROPDIR"
  else
    step=$((step + 1))
    echo
    echo "=== phase_c [$step/4] wire Main + build once ==="
    echo "    (already wired — skipping rewire, rebuilding $MODULE)"
    echo "    \$ lake build $MODULE"
    lake build "$MODULE"
    rc_build=$?
    if [ "$rc_build" -ne 0 ]; then
      echo
      echo "✗ phase_c STOPPED at step $step (wire Main + build once) — build failed (exit $rc_build)." >&2
      echo "  (scripts/phase_c.sh $PROPDIR --unwire to return to Phase B)" >&2
      exit "$rc_build"
    fi
  fi
  run_step "faithfulness (text + deps)"    scripts/check_faithful.sh "$MODULE"
  run_step "claim types unchanged"         python3 scripts/check_steps.py "$MAIN"
  run_step "proposition statements intact" python3 scripts/check_signatures.py

  echo
  echo "✓ phase_c: all 4 steps passed — $PROPDIR is FAITHFUL (gate C)."
  exit 0

else

# ═════════════════════════════════════════════════════════════════════════════
# MULTI-PROP MODE (quiet progress, errors only)
# ═════════════════════════════════════════════════════════════════════════════

  BOOK="$1"; shift
  resolve_props phase_c "$BOOK" "$@" || exit 2   # sets PROPS=(sorted propdirs)

  # ── run each prop; stay SILENT on pass, print captured output on fail ────────
  # A transient one-line "currently doing" status is shown when stderr is a terminal
  # (\r-overwritten, cleared at the end) so a passing run still ends concise.
  TOTAL="${#PROPS[@]}"
  N_FAIL=0; FAILED=()
  status() { [ -t 2 ] && printf '\r\033[K  ▸ [%d/%d] %s …' "$1" "$TOTAL" "$2" >&2; }
  clear_status() { [ -t 2 ] && printf '\r\033[K' >&2; }

  IDX=0
  for PROPDIR in "${PROPS[@]}"; do
    IDX=$((IDX + 1))
    status "$IDX" "$PROPDIR"
    OUT="$(bash "${BASH_SOURCE[0]}" "$PROPDIR" 2>&1)"
    if [ "$?" -ne 0 ]; then
      clear_status
      N_FAIL=$((N_FAIL + 1)); FAILED+=("$PROPDIR")
      echo "✗ FAIL  $PROPDIR"
      while IFS= read -r line; do echo "    $line"; done <<< "$OUT"
      echo
    fi
  done
  clear_status

  if [ "$N_FAIL" -eq 0 ]; then
    echo "✓ phase_c $BOOK: $TOTAL/$TOTAL passed (${PROPS[*]##*/})"
    exit 0
  fi
  echo "✗ phase_c $BOOK: $((TOTAL - N_FAIL))/$TOTAL passed, $N_FAIL failed — ${FAILED[*]##*/}"
  exit 1

fi
