#!/bin/bash
# Rename Book3/Prop33's hFG_int_AE sub-node backing files to the `hFG_int_AE_*` naming
# convention (Main-ancestor prefix), so the step_order_hook's prefix check resolves them.
# Renames files, rewrites theorem names + `have`/reference occurrences, drops the cert manifest.
set -euo pipefail
cd "$(dirname "$0")/LeanEuclidPlus/Book3/Prop33"

# Cone sub-nodes (NOT hFG_int_AE itself — that IS the Main node and keeps its name).
NODES="hbr1 hbr2 hbr3 hbr4 hle_e1 hsup_e1 hne_e0 hcon_ss hcon_ss_a hcon_ss_b hcon_os hos_tt hos_ff hos_tf hos_ft hb_ff hd_ff hb_offAD hd_offAB he0_offAB"

# 1. Rename existing backing files (hsup_e1 has no file yet — skipped).
for n in $NODES; do
  if [ -f "$n.lean" ]; then
    mv "$n.lean" "hFG_int_AE_$n.lean"
    echo "mv $n.lean -> hFG_int_AE_$n.lean"
  fi
done

# 2. Rewrite theorem names + all node-name references, longest-name-first for safety.
SORTED=$(printf '%s\n' $NODES | awk '{print length, $0}' | sort -rn | cut -d' ' -f2-)
FILES="Main.lean hFG_int_AE.lean"
for n in $NODES; do
  if [ -f "hFG_int_AE_$n.lean" ]; then FILES="$FILES hFG_int_AE_$n.lean"; fi
done
for f in $FILES; do
  for n in $SORTED; do
    # theorem defs: helper_3_33_<n>  ->  helper_3_33_hFG_int_AE_<n>
    sed -i -E "s/helper_3_33_${n}\b/helper_3_33_hFG_int_AE_${n}/g" "$f"
    # standalone node refs (have/exact/rcases/…): <n>  ->  hFG_int_AE_<n>
    # \b before <n> never matches inside helper_3_33_hFG_int_AE_<n> (preceded by '_'), so no double-prefix.
    sed -i -E "s/\b${n}\b/hFG_int_AE_${n}/g" "$f"
  done
done

# 3. Drop the stale cert manifest (will be rebuilt by the final audit).
rm -f "$(cd ../../ && pwd)/.lake/faithful-certified/Book3_Prop33.json"

echo "RENAME COMPLETE."
