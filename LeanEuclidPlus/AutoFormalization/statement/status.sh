#!/bin/bash
# Live status for running/finished runs: progress, tokens, cost, peak memory.
# Usage: bash status.sh [result_dir ...]   (defaults to the two opus48 dirs)
cd /h/56/taddmao/code/DNA/LeanEuclidPlus
DIRS=("$@")
[[ ${#DIRS[@]} -eq 0 ]] && DIRS=(result_opus48_base result_opus48_think_high)

echo "=== jobs ===" && squeue -u taddmao -o "%.12i %.8T %.10M %R" 2>/dev/null
for d in "${DIRS[@]}"; do
  echo ""; echo "======== $d ========"
  echo "  responses: $(find "$d"/response -name '*.txt' 2>/dev/null | wc -l)/500   statements: $(find "$d"/statement -name '*.json' 2>/dev/null | wc -l)"
  awk -F, 'NR>1 && $3+0>m{m=$3+0} END{if(m)printf "  peak mem: %.1f GB\n", m}' "$d"/mem_usage.csv 2>/dev/null
  python - "$d" <<'PY'
import re, glob, sys
d=sys.argv[1]; inp=out=cr=0; n=0
for f in glob.glob(f"{d}/response/**/*.txt", recursive=True):
    m=re.search(r"Accumulated Token Usage:\s*\n\s*\n(\{.*?\})", open(f).read(), re.DOTALL)
    if not m: continue
    n+=1
    for k in ("inputTokens","outputTokens","cacheReadInputTokens"):
        mm=re.search(rf'"{k}":\s*(\d+)', m.group(1))
        if mm:
            v=int(mm.group(1))
            inp+= v if k=="inputTokens" else 0
            out+= v if k=="outputTokens" else 0
            cr += v if k=="cacheReadInputTokens" else 0
if n:
    cost=inp/1e6*5+out/1e6*25+cr/1e6*0.5
    print(f"  tokens/{n}: in={inp:,} out={out:,} cacheRead={cr:,}")
    print(f"  cost so far ${cost:.2f}  -> projected full(500) ${cost*500/n:.2f}")
# headline if finished
import os
for s in glob.glob(f"{d}/equivalence/**/overall_summary.txt", recursive=True):
    for line in open(s):
        if "Equivalent Rate" in line or "Total Count" in line: print("  "+line.strip())
PY
done
