#!/bin/bash
# Generalized single-model run for LeanEuclidPlus (UniGeo, 100 core), 1-shot baseline (1_direct).
# Chained: autoformalize_pipeline.py -> evaluate.py -> analyze_results.py, with memory + timing.
#
# Driven by env vars (all optional; defaults reproduce the validated Sonnet baseline):
#   MODEL=<bedrock model id>          e.g. us.anthropic.claude-opus-4-8
#   RESULT_DIR=<dir name>             e.g. result_opus48_base
#   MAX_INSTANCES=<N>                 0 = all (full run); >0 = first N per category (pre-flight)
#   REUSE=<1|0>                       1 (default) = reuse saved responses (crash-resilient)
#
# Examples:
#   MODEL=us.anthropic.claude-opus-4-8 RESULT_DIR=result_opus48_base bash run_model.sh
#   MAX_INSTANCES=2 MODEL=... RESULT_DIR=... bash run_model.sh    # 2-instance pre-flight
set -euo pipefail

cd /h/56/taddmao/code/DNA/LeanEuclidPlus/AutoFormalization/statement
ROOT_DIR="$(cd ../.. && pwd)"

# --- config (1-shot baseline, identical to the validated Sonnet run except MODEL/RESULT_DIR) ---
MODEL="${MODEL:-us.anthropic.claude-sonnet-4-20250514-v1:0}"
RESULT_DIR="${RESULT_DIR:-result_run}"
MAX_INSTANCES="${MAX_INSTANCES:-0}"
DATASET="UniGeo"
CATEGORY="${CATEGORY:-Parallel Triangle Quadrilateral Congruent Similarity}"  # 5 x 20 = 100 core
METHOD="1_direct"
REASONING="text-only"
NUM_EXAMPLES=1                   # 1-shot
EXAMPLE_CHOICE="Similarity-1"
EXAMPLE_FORMAT="content"
TEMPERATURE=0.2                  # ignored by the Opus 4.8 branch (4.8 deprecates temperature)
NUM_QUERY=1
NUM_RUN="${NUM_RUN:-5}"
NUM_ASYNC_PRED=20
NUM_PROCESS_PRED=32              # OOM mitigation (100 workers OOM'd at 120G)
BATCH_SIZE_EVAL=5
NUM_PROCESS_EVAL=32

# Reuse-or-call: reuse saved responses when present, call the LLM only for missing ones.
# Crash-resilient and safe on a fresh dir. Set REUSE=0 to force fully fresh calls.
REUSE="${REUSE:-1}"
REUSE_FLAG=""
[[ "$REUSE" == "1" ]] && REUSE_FLAG="--reuse_responses"

RESULT_PATH="${ROOT_DIR}/${RESULT_DIR}"

echo "=================================================================="
echo "MODEL=$MODEL"
echo "RESULT_DIR=$RESULT_DIR   MAX_INSTANCES=$MAX_INSTANCES   REUSE=$REUSE"
echo "=================================================================="

# --- runtime stamp + passive memory monitor (observability; does not affect results) ---
START=$(date +%s)
echo "RUN START: $(date)"
mkdir -p "$RESULT_PATH"
MEM_CSV="${RESULT_PATH}/mem_usage.csv"
python mem_monitor.py --root-pid $$ --out "$MEM_CSV" --interval 15 &
MON_PID=$!
trap 'kill "$MON_PID" 2>/dev/null || true' EXIT
echo "📈 Memory monitor PID $MON_PID -> $MEM_CSV"

echo "=== [1/3] Inference: $MODEL ($METHOD, 1-shot, ${NUM_RUN} runs, max_instances=$MAX_INSTANCES) ==="
# `< <(yes)` (process substitution) auto-answers the REUSE=0 overwrite prompt without
# putting `yes` in a pipeline (which under set -o pipefail would SIGPIPE-abort the script).
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
python /h/56/taddmao/code/DNA/scripts/analyze_results.py \
  --result_dir "${RESULT_PATH}/equivalence" \
  --benchmark "$DATASET" \
  --mode "$REASONING" \
  --output_file "${RESULT_PATH}/UniGeo_results.xlsx" \
  || echo "(table builder failed/blank — ignore; read overall_summary.txt below)"

echo ""
echo "=================================================================="
echo "=== DONE: $MODEL — HEADLINE NUMBER (authoritative): ==="
echo "=================================================================="
find "${RESULT_PATH}/equivalence" -name overall_summary.txt | while read -r f; do
    echo "--- $f ---"
    grep -E "Overall (Total Count|Equivalent Count|Equivalent Rate|Validation Rate)" "$f" || cat "$f"
done
echo ""
echo "Excel (may be blank, see note): ${RESULT_PATH}/UniGeo_results.xlsx"

# --- runtime + peak-memory summary ---
END=$(date +%s)
ELAPSED=$((END - START))
echo ""
echo "RUN END: $(date)"
printf "Total elapsed: %dh %dm %ds\n" $((ELAPSED/3600)) $(((ELAPSED%3600)/60)) $((ELAPSED%60))
if [[ -f "$MEM_CSV" ]]; then
    awk -F, 'NR>1 && $3+0>max{max=$3+0} END{printf "Peak memory: %.1f GB (from %s)\n", max, FILENAME}' "$MEM_CSV"
fi
