#!/usr/bin/env bash
# Phase A gate script (the HUMAN runs this — see FAITHFUL.md "Phase A — sentence map").
# Runs the four Phase-A checks in order:
#   1. faithfulness (source/regex)   — python3 scripts/check_faithful.py
#   2. build (sorry ok)              — scripts/safe_build.sh
#   3. claim types (--save)          — python3 scripts/check_steps.py --save
#   4. assumption phase sweep        — python3 scripts/assumptions.py
#
# SINGLE-PROP (verbose, stops at first failure within the prop):
#   scripts/phase_a.sh Book3/Prop10
#   scripts/phase_a.sh Book3/Prop10/Main.lean   # Main.lean suffix tolerated
#   scripts/phase_a.sh Book3.Prop10.Main         # dotted module form tolerated
#
# MULTI-PROP (quiet — one line per prop, errors printed only on failure):
#   scripts/phase_a.sh Book3                     # all Prop* in Book3
#   scripts/phase_a.sh Book3 all                 # same
#   scripts/phase_a.sh Book3 4 5 6               # specific props (zero-pad optional)
#   scripts/phase_a.sh Book3 11-16               # a range, props 11..16
#   scripts/phase_a.sh Book3 11-                 # prop 11 to the end of the book
#   scripts/phase_a.sh Book3 1 10-14 20          # mix singles + ranges (commas ok too)
#
# Assumption flags (apply to both modes):
#   --skip_assumptions      skip the assumptions sweep entirely
#   --override_assumptions  if already materialized, re-run without prompting (auto-yes)
#   (default)               if already materialized, ask y/N before re-running
#
# Exit code: 0 iff all props passed; non-zero on any failure.

set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"   # LeanEuclidPlus/
cd "$HERE"
source "$HERE/scripts/prop_select.sh"                     # shared BOOK/range selector grammar

VENV="${LEANEUCLID_VENV:-$HOME/.venvs/leaneuclid}"
if [ -d "$VENV/bin" ]; then
  export PATH="$VENV/bin:$PATH"
fi

# ── parse flags ───────────────────────────────────────────────────────────────
SKIP_ASSUMPTIONS=0
OVERRIDE_ASSUMPTIONS=0
POSITIONAL=()
for arg in "$@"; do
  case "$arg" in
    --skip_assumptions)    SKIP_ASSUMPTIONS=1 ;;
    --override_assumptions) OVERRIDE_ASSUMPTIONS=1 ;;
    *) POSITIONAL+=("$arg") ;;
  esac
done
set -- "${POSITIONAL[@]+"${POSITIONAL[@]}"}"

[ "$#" -lt 1 ] && { echo "usage: scripts/phase_a.sh <propdir|book> [props…|all] [--skip_assumptions|--override_assumptions]" >&2; exit 2; }

# ── assumptions step helper ───────────────────────────────────────────────────
run_assumptions_step() {
  local propdir="$1"
  local main="$propdir/Main.lean"

  if [ "$SKIP_ASSUMPTIONS" -eq 1 ]; then
    echo "    (assumptions skipped by --skip_assumptions)"
    return 0
  fi

  if grep -q "@assumption_valid\|@assumption_gap" "$main" 2>/dev/null; then
    # Already materialized
    if [ "$OVERRIDE_ASSUMPTIONS" -eq 1 ]; then
      echo "y" | python3 scripts/assumptions.py "$propdir"
    else
      printf "\n    Assumptions already materialized in %s. Re-run from scratch? [y/N] " "$propdir"
      read -r ans </dev/tty
      if [[ "$ans" =~ ^[Yy] ]]; then
        echo "y" | python3 scripts/assumptions.py "$propdir"
      else
        echo "    (skipping assumptions re-run — using existing materialization)"
        return 0
      fi
    fi
  else
    python3 scripts/assumptions.py "$propdir"
  fi
}

# ── detect mode ───────────────────────────────────────────────────────────────
if [[ "$1" == *"/"* ]] || [[ "$1" =~ [Pp]rop ]]; then

# ═════════════════════════════════════════════════════════════════════════════
# SINGLE-PROP MODE (compact: one line per check, full error only on failure)
# ═════════════════════════════════════════════════════════════════════════════

  RAW="$1"; RAW="${RAW%/Main.lean}"; RAW="${RAW%/}"
  PROPDIR="${RAW//./\/}"
  MODULE="${PROPDIR//\//.}.Main"
  MAIN="$PROPDIR/Main.lean"

  [ ! -f "$MAIN" ] && { echo "phase_a: no $MAIN under $HERE" >&2; exit 2; }

  step=0
  run_step() {
    step=$((step + 1))
    local label="$1"; shift
    printf "  [%d/4] %-34s" "$step" "$label"
    OUT="$("$@" 2>&1)"
    local rc=$?
    if [ "$rc" -eq 0 ]; then
      echo "PASS"
    else
      echo "FAIL"
      echo
      while IFS= read -r line; do echo "        $line"; done <<< "$OUT"
      echo
      echo "✗ stopped at step $step ($label) — fix it, then re-run scripts/phase_a.sh $PROPDIR." >&2
      exit "$rc"
    fi
  }

  echo "Phase A: $PROPDIR"
  echo
  run_step "faithfulness (source/regex)"  python3 scripts/check_faithful.py "$MAIN"
  run_step "build (sorry ok)"             scripts/safe_build.sh "$MODULE"
  run_step "claim types (--save)"         python3 scripts/check_steps.py --save "$MAIN"

  # Assumptions: interactive logic — handle separately so prompt goes to terminal
  step=$((step + 1))
  printf "  [%d/4] %-34s" "$step" "assumption phase sweep"
  if [ "$SKIP_ASSUMPTIONS" -eq 1 ]; then
    echo "SKIP"
  elif grep -q "@assumption_valid\|@assumption_gap" "$MAIN" 2>/dev/null; then
    if [ "$OVERRIDE_ASSUMPTIONS" -eq 1 ]; then
      OUT="$(echo "y" | python3 scripts/assumptions.py "$PROPDIR" 2>&1)"; rc=$?
      [ "$rc" -eq 0 ] && echo "PASS" || { echo "FAIL"; echo; while IFS= read -r line; do echo "        $line"; done <<< "$OUT"; echo; exit "$rc"; }
    else
      echo ""
      printf "      already materialized — re-run from scratch? [y/N] "
      read -r ans </dev/tty
      if [[ "$ans" =~ ^[Yy] ]]; then
        OUT="$(echo "y" | python3 scripts/assumptions.py "$PROPDIR" 2>&1)"; rc=$?
        [ "$rc" -eq 0 ] && echo "      PASS" || { echo "      FAIL"; echo; while IFS= read -r line; do echo "        $line"; done <<< "$OUT"; echo; exit "$rc"; }
      else
        echo "      SKIP (kept existing materialization)"
      fi
    fi
  else
    OUT="$(python3 scripts/assumptions.py "$PROPDIR" 2>&1)"; rc=$?
    [ "$rc" -eq 0 ] && echo "PASS" || { echo "FAIL"; echo; while IFS= read -r line; do echo "        $line"; done <<< "$OUT"; echo; exit "$rc"; }
  fi

  echo
  echo "✓ all passed — $PROPDIR gate-A approved."
  exit 0

else

# ═════════════════════════════════════════════════════════════════════════════
# MULTI-PROP MODE (quiet progress, errors only)
# ═════════════════════════════════════════════════════════════════════════════

  BOOK="$1"; shift
  resolve_props phase_a "$BOOK" "$@" || exit 2   # sets PROPS=(sorted propdirs)

  TOTAL="${#PROPS[@]}"
  N_PASS=0; N_FAIL=0
  FAILED=()

  # Rebuild flag string to pass through to single-prop invocations
  FLAGS=()
  [ "$SKIP_ASSUMPTIONS" -eq 1 ]    && FLAGS+=("--skip_assumptions")
  [ "$OVERRIDE_ASSUMPTIONS" -eq 1 ] && FLAGS+=("--override_assumptions")

  echo "Phase A — $BOOK  ($TOTAL prop(s))"
  echo

  for i in "${!PROPS[@]}"; do
    PROPDIR="${PROPS[$i]}"
    IDX=$((i + 1))
    printf "  [%d/%d] %-24s" "$IDX" "$TOTAL" "$PROPDIR"

    OUT="$(bash "${BASH_SOURCE[0]}" "$PROPDIR" "${FLAGS[@]+"${FLAGS[@]}"}" 2>&1)"
    RC=$?

    if [ "$RC" -eq 0 ]; then
      echo "PASS"
      N_PASS=$((N_PASS + 1))
    else
      echo "FAIL"
      N_FAIL=$((N_FAIL + 1))
      FAILED+=("$PROPDIR")
      while IFS= read -r line; do echo "        $line"; done <<< "$OUT"
      echo
    fi
  done

  echo
  echo "─────────────────────────────────────────"
  if [ "$N_FAIL" -eq 0 ]; then
    echo "✓ $N_PASS/$TOTAL PASS — all props gate-A approved."
  else
    echo "✗ $N_PASS/$TOTAL PASS, $N_FAIL FAIL"
    echo "  Failed: ${FAILED[*]}"
  fi

  [ "$N_FAIL" -eq 0 ] && exit 0 || exit 1

fi
