#!/usr/bin/env bash
# Grab ONE exclusive CPU node, then run a command on it (or drop into a shell).
#   bash scripts/faithful_slurm.sh                                              # interactive shell
#   bash scripts/faithful_slurm.sh python3 scripts/run_faithful.py assumptions Book1/Prop02 … --concurrency 7
#
# WHY --exclusive: these nodes run vm.overcommit_memory=2 (strict). Each `claude` reserves ~70 GB of
# VIRTUAL address space (real use ~0.5 GB), and the kernel charges that reservation against a fixed,
# NODE-WIDE commit budget shared by every job. --mem is only an RSS cap — it can't buy commit budget.
# The only lever is owning the whole node, so no other job is eating the budget.
# On the node: concurrency ≈ (CommitLimit − Committed_AS) / 70 GB  (see /proc/meminfo).
# Add --partition=… / --account=… if your cluster requires them. No GPU is involved.
srun --exclusive --time=08:00:00 --pty "${@:-bash}"
