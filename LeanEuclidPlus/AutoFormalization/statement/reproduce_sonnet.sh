#!/bin/bash
# Reproduce the DNA paper's Sonnet *baseline* on LeanEuclidPlus (UniGeo, 100 core).
# Target number: Claude-4-Sonnet baseline ~= 34.2 (Table 3, non-reasoning).
# Chained: autoformalize_pipeline.py -> evaluate.py -> scripts/analyze_results.py (table).
#
# SMOKE TEST: run `SMOKE=1 bash reproduce_sonnet.sh` to do a tiny 1-category,
# 1-run, 3-problem dry run into a separate result dir, to confirm the plumbing
# works (API auth, solvers, file layout) before committing to the full overnight job.
set -euo pipefail

cd /h/56/taddmao/code/DNA/LeanEuclidPlus/AutoFormalization/statement

# The pipeline writes results under its ROOT_DIR (= ../.. from this statement dir,
# i.e. LeanEuclidPlus/), NOT the cwd. Anchor all our paths (mem CSV, table, headline
# summary) to the same place so everything for one run lives in one folder.
ROOT_DIR="$(cd ../.. && pwd)"

# --- config (paper baseline, non-reasoning Sonnet) ---
MODEL="us.anthropic.claude-sonnet-4-20250514-v1:0"
DATASET="UniGeo"
CATEGORY="Parallel Triangle Quadrilateral Congruent Similarity"  # 5 x 20 = 100 core
METHOD="1_direct"                # baseline (no decomposition)
REASONING="text-only"
NUM_EXAMPLES=1                   # 1-shot
EXAMPLE_CHOICE="Similarity-1"    # the single in-context example
EXAMPLE_FORMAT="content"
TEMPERATURE=0.2                  # non-reasoning models
NUM_QUERY=1                      # baseline = single query, no retry
NUM_RUN=5                        # paper samples 5 runs, reports pass@1 averaged
NUM_ASYNC_PRED=20
NUM_PROCESS_PRED=32              # lowered from 100: 100 loky workers x SMT solvers OOM'd at 120G
BATCH_SIZE_EVAL=5
NUM_PROCESS_EVAL=32             # same OOM mitigation for the eval stage (result-neutral)
RESULT_DIR="result_reproduce_sonnet"
MAX_INSTANCES=0                 # 0 = all instances (full run). SMOKE sets this to 2.

# Reuse already-saved responses when present (reuse-or-call): makes reruns cheap and
# crash-resilient, and is safe on a fresh dir (nothing to reuse -> calls everything).
# Set REUSE=0 to force a clean run that re-calls the LLM for every instance.
REUSE="${REUSE:-1}"
REUSE_FLAG=""
[[ "$REUSE" == "1" ]] && REUSE_FLAG="--reuse_responses"

# --- smoke-test overrides (tiny, fast, isolated) ---
if [[ "${SMOKE:-0}" == "1" ]]; then
    echo "### SMOKE TEST MODE: tiny dry run, NOT the paper number ###"
    CATEGORY="Parallel"          # single category
    NUM_RUN=1
    NUM_PROCESS_PRED=3
    NUM_PROCESS_EVAL=3
    NUM_ASYNC_PRED=3
    MAX_INSTANCES=2              # only 2 problems -> finishes in ~30s
    RESULT_DIR="result_smoke_sonnet"
fi

# Absolute path to this run's results dir (where the pipeline writes statement/response/equivalence).
RESULT_PATH="${ROOT_DIR}/${RESULT_DIR}"

# --- runtime stamp + passive memory monitor (observability; does not affect results) ---
START=$(date +%s)
echo "RUN START: $(date)"
mkdir -p "$RESULT_PATH"
MEM_CSV="${RESULT_PATH}/mem_usage.csv"
python mem_monitor.py --root-pid $$ --out "$MEM_CSV" --interval 15 &
MON_PID=$!
# Always stop the monitor when this script exits (success, error, or kill).
trap 'kill "$MON_PID" 2>/dev/null || true' EXIT
echo "📈 Memory monitor PID $MON_PID -> $MEM_CSV"

echo "=== [1/3] Inference: $MODEL ($METHOD, 1-shot, ${NUM_RUN} runs) ==="
# Feed "y" to the interactive overwrite prompt via process substitution. In reuse mode
# the prompt is skipped anyway; in REUSE=0 mode this auto-confirms the wipe so a batch
# job never hangs. We use `< <(yes)` rather than `yes | python` on purpose: with
# `set -o pipefail`, `yes` gets SIGPIPE when python exits and its non-zero status would
# abort the script (set -e) right after a SUCCESSFUL stage 1, silently skipping eval.
# Process substitution keeps `yes` out of the pipeline so its exit status is ignored.
python autoformalize_pipeline.py < <(yes) \
  --dataset "$DATASET" \
  --category $CATEGORY \
  --reasoning "$REASONING" \
  --num_query "$NUM_QUERY" \
  --num_examples "$NUM_EXAMPLES" \
  --example_choices "$EXAMPLE_CHOICE" \
  --example_format "$EXAMPLE_FORMAT" \
  --cot_for_reasoning_models full \
  --method "$METHOD" \
  --model "$MODEL" \
  --num_process "$NUM_PROCESS_PRED" \
  --num_async "$NUM_ASYNC_PRED" \
  --enable_caching \
  --temperature "$TEMPERATURE" \
  --num_run "$NUM_RUN" \
  --relations_file Relations_barebone \
  --dsl_doc doc_barebone.txt \
  --result_dir_name "$RESULT_DIR" \
  --max_instances "$MAX_INSTANCES" \
  $REUSE_FLAG

echo "=== [2/3] Evaluation (E3 equivalence checking) ==="
python evaluate.py \
  --dataset "$DATASET" \
  --category $CATEGORY \
  --reasoning "$REASONING" \
  --num_examples "$NUM_EXAMPLES" \
  --example_choices "$EXAMPLE_CHOICE" \
  --method "$METHOD" \
  --model "$MODEL" \
  --num_process "$NUM_PROCESS_EVAL" \
  --batch_size "$BATCH_SIZE_EVAL" \
  --num_run "$NUM_RUN" \
  --ground_relations_file Relations \
  --test_relations_file Relations_barebone \
  --result_dir_name "$RESULT_DIR" \
  --max_instances "$MAX_INSTANCES"

echo "=== [3/3] Build results table (best-effort; authoritative number is below) ==="
# NOTE: scripts/analyze_results.py greps for "Total Compilation/Equivalent Rate",
# but this evaluate.py writes "Overall Equivalent Rate" (no compilation rate), so the
# Excel cells may be blank. The overall_summary.txt below is the source of truth.
python /h/56/taddmao/code/DNA/scripts/analyze_results.py \
  --result_dir "${RESULT_PATH}/equivalence" \
  --benchmark "$DATASET" \
  --mode "$REASONING" \
  --output_file "${RESULT_PATH}/UniGeo_results.xlsx" \
  || echo "(table builder failed/blank — ignore; read overall_summary.txt below)"

echo ""
echo "=================================================================="
echo "=== DONE. HEADLINE NUMBER (authoritative): ==="
echo "=================================================================="
find "${RESULT_PATH}/equivalence" -name overall_summary.txt | while read -r f; do
    echo "--- $f ---"
    grep -E "Overall (Total Count|Equivalent Count|Equivalent Rate|Validation Rate)" "$f" || cat "$f"
done
echo ""
echo "Compare 'Overall Equivalent Rate' against paper Table 3 Sonnet baseline ~= 0.342"
echo "Excel (may be blank, see note): ${RESULT_PATH}/UniGeo_results.xlsx"

# --- runtime + peak-memory summary ---
END=$(date +%s)
ELAPSED=$((END - START))
echo ""
echo "RUN END: $(date)"
printf "Total elapsed: %dh %dm %ds\n" $((ELAPSED/3600)) $(((ELAPSED%3600)/60)) $((ELAPSED%60))
if [[ -f "$MEM_CSV" ]]; then
    # peak of the total_rss_gb column (col 3), skipping the header
    awk -F, 'NR>1 && $3+0>max{max=$3+0} END{printf "Peak memory: %.1f GB (from %s)\n", max, FILENAME}' "$MEM_CSV"
fi
