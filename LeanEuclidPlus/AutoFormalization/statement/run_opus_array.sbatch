#!/bin/bash
#SBATCH --job-name=dna-opus48
#SBATCH --partition=cpunodes
#SBATCH --cpus-per-task=64
#SBATCH --mem=300G
#SBATCH --time=12:00:00
#SBATCH --array=0-1
#SBATCH --output=/h/56/taddmao/code/DNA/LeanEuclidPlus/AutoFormalization/statement/slurm-%A_%a.out
#SBATCH --error=/h/56/taddmao/code/DNA/LeanEuclidPlus/AutoFormalization/statement/slurm-%A_%a.out

# Array job: one task per Opus 4.8 variant.
#   index 0 -> opus-4-8              (non-thinking)         -> result_opus48_base
#   index 1 -> opus-4-8-thinking-high (adaptive high effort) -> result_opus48_think_high
#
# Full run:        sbatch run_opus_array.sbatch
# 2-instance test: MAX_INSTANCES=2 sbatch --export=ALL,MAX_INSTANCES=2 run_opus_array.sbatch
#   (then inspect result_opus48_*/response/.../*.txt token usage before the full run)

set -euo pipefail
source /u/taddmao/.venvs/leaneuclid/bin/activate
cd /h/56/taddmao/code/DNA/LeanEuclidPlus/AutoFormalization/statement

MODELS=( "us.anthropic.claude-opus-4-8" "us.anthropic.claude-opus-4-8-thinking-high" )
DIRS=(   "result_opus48_base"           "result_opus48_think_high" )

export MODEL="${MODELS[$SLURM_ARRAY_TASK_ID]}"
export RESULT_DIR="${DIRS[$SLURM_ARRAY_TASK_ID]}"
export MAX_INSTANCES="${MAX_INSTANCES:-0}"   # 0 = full run; override to e.g. 2 for pre-flight

echo "Array task $SLURM_ARRAY_TASK_ID -> MODEL=$MODEL RESULT_DIR=$RESULT_DIR MAX_INSTANCES=$MAX_INSTANCES"
bash run_model.sh
