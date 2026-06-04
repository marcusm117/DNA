#!/bin/bash
#SBATCH --job-name=dna-sonnet-baseline
#SBATCH --partition=cpunodes
#SBATCH --cpus-per-task=64
#SBATCH --mem=480G
#SBATCH --time=12:00:00
#SBATCH --output=/h/56/taddmao/code/DNA/LeanEuclidPlus/AutoFormalization/statement/slurm-%j.out
#SBATCH --error=/h/56/taddmao/code/DNA/LeanEuclidPlus/AutoFormalization/statement/slurm-%j.out

# Wrapper that runs the chained reproduction (inference -> evaluate -> table) under Slurm.
# Submit with:  sbatch reproduce_sonnet.sbatch
# Smoke test:   SMOKE=1 sbatch reproduce_sonnet.sbatch   (or run bash directly, see below)

set -euo pipefail

# Activate the env that has z3 / cvc5 / smt-portfolio (a venv, NOT conda base).
source /u/taddmao/.venvs/leaneuclid/bin/activate

# Run the chained pipeline (inference -> evaluate -> table). Bedrock creds are
# auto-loaded by the code from AutoFormalization/.env, so nothing to set here.
cd /h/56/taddmao/code/DNA/LeanEuclidPlus/AutoFormalization/statement
bash reproduce_sonnet.sh
