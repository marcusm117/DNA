# prop_select.sh — shared prop-selection grammar for the phase_*.sh scripts.
#
# SOURCE it (don't execute), then call:
#     resolve_props <who> <BOOK> [selector…]
# On success it sets the global array PROPS=(dir …), sorted numerically + de-duped,
# and returns 0. On a hard error (bad book dir / nothing selected) it prints to
# stderr and returns 2. Individual missing/out-of-range numbers are skipped with a
# stderr note (not a hard error).
#
# Selector grammar — IDENTICAL across every phase_*.sh:
#     (none) | all      every Prop*/ in the book
#     N                 a single prop            (leading "Prop" and zero-pad optional)
#     N-M               inclusive range  N..M
#     N-                N to the LAST prop in the book
#     N,M,K             commas tolerated as separators (same as spaces)
# e.g.  Book3   ·   Book3 all   ·   Book3 11-16   ·   Book3 11-   ·   Book3 1 10-14 20   ·   Book3 1,10,2

resolve_props() {
  local who="$1" book="$2"; shift 2
  PROPS=()
  [ -d "$book" ] || { echo "$who: directory not found: '$book'" >&2; return 2; }

  # available props: number -> propdir, plus the max number in the book
  local -A avail=(); local maxn=0 d base raw n
  for d in "$book"/Prop*/; do
    [ -f "${d}Main.lean" ] || continue
    base="${d%/}"; raw="${base##*/Prop}"
    [[ "$raw" =~ ^[0-9]+$ ]] || continue
    n=$((10#$raw)); avail[$n]="$base"
    (( n > maxn )) && maxn=$n
  done
  [ "${#avail[@]}" -eq 0 ] && { echo "$who: no Prop*/Main.lean found in $book" >&2; return 2; }

  # selection
  local sel=() arg tok lo hi
  if [ "$#" -eq 0 ] || { [ "$#" -eq 1 ] && [ "${1:-}" = "all" ]; }; then
    sel=("${!avail[@]}")
  else
    for arg in "$@"; do
      arg="${arg//,/ }"                          # commas act as separators
      for tok in $arg; do
        tok="${tok#Prop}"; tok="${tok#prop}"     # strip optional Prop prefix
        if   [[ "$tok" =~ ^([0-9]+)-([0-9]+)$ ]]; then
          lo=$((10#${BASH_REMATCH[1]})); hi=$((10#${BASH_REMATCH[2]}))
          for ((n=lo; n<=hi; n++)); do [ -n "${avail[$n]:-}" ] && sel+=("$n"); done
        elif [[ "$tok" =~ ^([0-9]+)-$ ]]; then
          lo=$((10#${BASH_REMATCH[1]}))
          for ((n=lo; n<=maxn; n++)); do [ -n "${avail[$n]:-}" ] && sel+=("$n"); done
        elif [[ "$tok" =~ ^[0-9]+$ ]]; then
          n=$((10#$tok))
          if [ -n "${avail[$n]:-}" ]; then sel+=("$n"); else echo "$who: no $book/Prop$tok — skipping" >&2; fi
        else
          echo "$who: unrecognized selector '$tok' — skipping" >&2
        fi
      done
    done
    [ "${#sel[@]}" -eq 0 ] && { echo "$who: no valid props selected" >&2; return 2; }
  fi

  mapfile -t sel < <(printf '%s\n' "${sel[@]}" | sort -n -u)
  PROPS=(); for n in "${sel[@]}"; do PROPS+=("${avail[$n]}"); done
  return 0
}
