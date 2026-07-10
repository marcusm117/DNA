#!/usr/bin/env bash
# Phase A status checker — reports which props are missing Phase-A artifacts.
# Reads source files only (no builds). Prints only props with issues.
#
# Usage:
#   scripts/phase_a_check.sh Book3           # all Prop* in Book3
#   scripts/phase_a_check.sh Book3 4-11      # props 4 through 11
#   scripts/phase_a_check.sh Book3 4 6 10    # specific props (mix of ranges and singles ok)
#
# Checks per prop:
#   1. mapped        — has euclid_sentence steps
#   2. no True       — no (step : True) placeholders from faithful-map
#   3. no TODO       — no @assumption TODO annotations from faithful-map
#   4. sigs saved    — appears in step_signatures.json (check_steps --save done)
#   5. assumptions   — @assumption annotations have been swept (valid/gap tags present)
#
# Exit: 0 all ok, 1 any issues found.

set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"   # LeanEuclidPlus/
cd "$HERE"

SIGS="scripts/step_signatures.json"

[ "$#" -lt 1 ] && { echo "usage: scripts/phase_a_check.sh <book> [range|props…]" >&2; exit 2; }

BOOK="$1"; shift
[ ! -d "$BOOK" ] && { echo "phase_a_check: directory not found: '$BOOK'" >&2; exit 2; }

# ── collect props ─────────────────────────────────────────────────────────────
PROPS=()
if [ "$#" -eq 0 ]; then
  for d in "$BOOK"/Prop*/; do
    [ -f "${d}Main.lean" ] && PROPS+=("${d%/}")
  done
  [ "${#PROPS[@]}" -eq 0 ] && { echo "phase_a_check: no Prop*/Main.lean found in $BOOK" >&2; exit 2; }
else
  for arg in "$@"; do
    if [[ "$arg" == *-* ]] && [[ "$arg" =~ ^[0-9]+-[0-9]+$ ]]; then
      # Range: e.g. 4-11
      LO="${arg%-*}"; HI="${arg#*-}"
      for (( n = 10#$LO; n <= 10#$HI; n++ )); do
        printf -v padded "%02d" "$n"
        d="$BOOK/Prop$padded"
        if [ -f "$d/Main.lean" ]; then
          PROPS+=("$d")
        else
          echo "  [skip] $d — no Main.lean" >&2
        fi
      done
    else
      n="${arg#Prop}"
      printf -v padded "%02d" "$((10#$n))" 2>/dev/null || padded="$n"
      d="$BOOK/Prop$padded"
      if [ -f "$d/Main.lean" ]; then
        PROPS+=("$d")
      else
        echo "  [skip] $d — no Main.lean" >&2
      fi
    fi
  done
  [ "${#PROPS[@]}" -eq 0 ] && { echo "phase_a_check: no valid props found" >&2; exit 2; }
fi

# ── check each prop ───────────────────────────────────────────────────────────
TOTAL="${#PROPS[@]}"
N_OK=0; N_ISSUE=0

echo "Phase A check — $BOOK  ($TOTAL prop(s))"
echo

for PROPDIR in "${PROPS[@]}"; do
  MAIN="$PROPDIR/Main.lean"
  ISSUES=()

  # 1. Mapped?
  if ! grep -q "euclid_sentence" "$MAIN" 2>/dev/null; then
    ISSUES+=("not mapped (no euclid_sentence steps)")
  else

    # 2. True placeholders?
    if grep -qE '\(step[0-9a-z_]+ : True\)' "$MAIN" 2>/dev/null; then
      count=$(grep -cE '\(step[0-9a-z_]+ : True\)' "$MAIN" 2>/dev/null || true)
      ISSUES+=("$count True placeholder claim(s) — faithful-map incomplete")
    fi

    # 3. @assumption TODO?
    if grep -q "@assumption TODO" "$MAIN" 2>/dev/null; then
      count=$(grep -c "@assumption TODO" "$MAIN" 2>/dev/null || true)
      ISSUES+=("$count @assumption TODO(s) — faithful-map incomplete")
    fi

    # 4. Signatures saved? (step_signatures.json has a "file" entry for this prop)
    REL_PATH="${PROPDIR}/Main.lean"
    if [ ! -f "$SIGS" ]; then
      ISSUES+=("step_signatures.json missing")
    elif ! grep -q "\"$REL_PATH\"" "$SIGS" 2>/dev/null; then
      ISSUES+=("not in step_signatures.json — check_steps --save not run")
    fi

    # 5. Assumptions swept?
    N_ANNOT=$(grep -c "^[[:space:]]*-- @assumption (" "$MAIN" 2>/dev/null || true)
    N_TAGGED=$(grep -c "@assumption_valid\|@assumption_gap" "$MAIN" 2>/dev/null || true)
    if [ "$N_ANNOT" -gt 0 ] && [ "$N_TAGGED" -eq 0 ]; then
      ISSUES+=("$N_ANNOT @assumption(s) not swept — run scripts/assumptions.py $PROPDIR")
    fi

  fi

  if [ "${#ISSUES[@]}" -eq 0 ]; then
    N_OK=$((N_OK + 1))
  else
    N_ISSUE=$((N_ISSUE + 1))
    printf "  %-26s\n" "$PROPDIR"
    for issue in "${ISSUES[@]}"; do
      echo "      • $issue"
    done
  fi
done

echo
echo "─────────────────────────────────────────"
if [ "$N_ISSUE" -eq 0 ]; then
  echo "✓ $N_OK/$TOTAL — all gate-A complete."
else
  echo "✗ $N_OK/$TOTAL ok, $N_ISSUE with issues"
fi

[ "$N_ISSUE" -eq 0 ] && exit 0 || exit 1
