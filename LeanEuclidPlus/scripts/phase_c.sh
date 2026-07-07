#!/usr/bin/env bash
# Phase C wrapper (the HUMAN runs this — see FAITHFUL.md "Phase C — wire + verify").
#
# SINGLE-PROP (verbose, stops at first failure within the prop):
#   scripts/phase_c.sh Book3/Prop04
#   scripts/phase_c.sh Book3/Prop04/Main.lean   # Main.lean suffix tolerated
#   scripts/phase_c.sh Book3.Prop04.Main         # dotted module form tolerated
#   scripts/phase_c.sh Book3/Prop04 --unwire     # reverse wiring back to Phase-B
#
# MULTI-PROP (quiet — one line per prop, errors printed only on failure):
#   scripts/phase_c.sh Book3                     # all Prop* in Book3
#   scripts/phase_c.sh Book3 all                 # same
#   scripts/phase_c.sh Book3 04 05 06            # specific props (zero-pad optional)
#
# Exit code: 0 iff all props passed; non-zero on any failure.

set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"   # LeanEuclidPlus/
cd "$HERE"

[ "$#" -lt 1 ] && { echo "usage: scripts/phase_c.sh <propdir|book> [props…|all] [--unwire]" >&2; exit 2; }

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

  [ ! -d "$BOOK" ] && { echo "phase_c: directory not found: '$BOOK'" >&2; exit 2; }

  # Collect prop directories
  PROPS=()
  if [ "$#" -eq 0 ] || { [ "$#" -eq 1 ] && [ "${1:-}" = "all" ]; }; then
    for d in "$BOOK"/Prop*/; do
      [ -f "${d}Main.lean" ] && PROPS+=("${d%/}")
    done
    [ "${#PROPS[@]}" -eq 0 ] && { echo "phase_c: no Prop*/Main.lean found in $BOOK" >&2; exit 2; }
  else
    for n in "$@"; do
      n="${n#Prop}"                              # strip leading "Prop" if given
      printf -v padded "%02d" "$((10#$n))" 2>/dev/null || padded="$n"
      d="$BOOK/Prop$padded"
      if [ -f "$d/Main.lean" ]; then
        PROPS+=("$d")
      else
        echo "phase_c: no $d/Main.lean — skipping" >&2
      fi
    done
    [ "${#PROPS[@]}" -eq 0 ] && { echo "phase_c: no valid props found" >&2; exit 2; }
  fi

  TOTAL="${#PROPS[@]}"
  N_PASS=0; N_FAIL=0
  FAILED=()

  echo "Phase C — $BOOK  ($TOTAL prop(s))"
  echo

  for i in "${!PROPS[@]}"; do
    PROPDIR="${PROPS[$i]}"
    IDX=$((i + 1))
    printf "  [%d/%d] %-24s" "$IDX" "$TOTAL" "$PROPDIR"

    OUT="$(bash "${BASH_SOURCE[0]}" "$PROPDIR" 2>&1)"
    RC=$?

    if [ "$RC" -eq 0 ]; then
      echo "PASS"
      N_PASS=$((N_PASS + 1))
    else
      echo "FAIL"
      N_FAIL=$((N_FAIL + 1))
      FAILED+=("$PROPDIR")
      # Re-indent and print the captured output so the failure is readable
      while IFS= read -r line; do echo "        $line"; done <<< "$OUT"
      echo
    fi
  done

  echo
  echo "─────────────────────────────────────────"
  if [ "$N_FAIL" -eq 0 ]; then
    echo "✓ $N_PASS/$TOTAL PASS — all props faithful."
  else
    echo "✗ $N_PASS/$TOTAL PASS, $N_FAIL FAIL"
    echo "  Failed: ${FAILED[*]}"
  fi

  [ "$N_FAIL" -eq 0 ] && exit 0 || exit 1

fi
