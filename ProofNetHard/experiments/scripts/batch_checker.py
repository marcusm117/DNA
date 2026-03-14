#!/usr/bin/env python3
from __future__ import annotations

"""
Batch checker: traverse a root directory and run the ProofNet equivalence
checker for every run folder that contains a results JSON.

A "run folder" is any directory that contains exactly one "*_result.json"
produced by the autoformalization pipeline.

Examples:
  python experiments/scripts/batch_checker.py \
      --root outputs/exeperiments_2025-09-21_12-00-00 \
      --num_concurrency 100 --timeout 60
"""

import argparse
import glob
import os
import subprocess
import sys
from typing import Iterator, Tuple, Optional

DEFAULT_STRATEGIES = ['beq_plus']  # robust default (BEq+ only)
LLM_URL_DEFAULT = 'https://openrouter.ai/api/v1'
LLM_MODEL_DEFAULT = 'qwen/qwen3-235b-a22b-2507'


def iter_run_folders(root: str) -> Iterator[Tuple[str, str]]:
    """Yield (run_dir, results_json) pairs under root.

    Strategy: look one level down for directories; in each, find a single
    file that matches "*_result.json".
    """
    if not os.path.isdir(root):
        return
    for name in sorted(os.listdir(root)):
        run_dir = os.path.join(root, name)
        if not os.path.isdir(run_dir):
            continue
        candidates = glob.glob(os.path.join(run_dir, '*_result.json'))
        if not candidates:
            continue
        # pick the first match (usually the only one)
        yield run_dir, candidates[0]


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description='Batch runner for ProofNet equivalence checker')
    p.add_argument('--root', required=True, help='Root directory that contains run folders')
    p.add_argument('--strategies', nargs='+', default=DEFAULT_STRATEGIES, choices=['beq_plus'])
    p.add_argument('--num_concurrency', type=int, default= 200)
    p.add_argument('--timeout', type=int, default=240)
    p.add_argument('--lean_version', default='v4.7.0-rc2')
    p.add_argument('--stat_mode', default='per_prediction', choices=['per_problem', 'per_prediction'])
    # Optional: redirect outputs away from the run folder
    p.add_argument('--output_root', default=None, help='If set, write outputs under this directory using each run folder name')
    # Limit total tasks (problem×prediction×strategy×direction) inside the checker
    p.add_argument('--limit_tasks', type=int, default=None, help='Debug: limit total tasks created inside checker')
    # Dataset and experiment type for relations/header resolution
    p.add_argument('--dataset', default=None, help='Dataset name for checker (e.g., DSL). If omitted, auto-infer')
    p.add_argument('--experiment_type', choices=['learned', 'oracle', 'barebone'], default=None,
                   help='Experiment type to choose relations (overrides inference from paths)')
    # Lean env roots (optional; required for BEQ strategies)
    p.add_argument('--root_dir', default=os.getcwd())
    p.add_argument('--mathlib_root', default='lean-env/mathlib4')
    p.add_argument('--repl_root', default='lean-env/repl')
    # Optional ground-truth source for headers/formal (DSL)
    p.add_argument('--gt_csv', default=None, help='Path to DSL ground-truth CSV (e.g., data/proofnet_dsl/ProofNet-Lean4_proof_dsl.csv)')
    # LLM (optional if llm in strategies); URL/Model are fixed to OpenRouter + Qwen3-235B in this batch script
    p.add_argument('--generate_queries', type=int, default=8)
    p.add_argument('--num_samples', type=int, default=1)
    p.add_argument('--max_tokens', type=int, default=2048)
    p.add_argument('--temperature', type=float, default=0.2)
    # Debug helpers
    p.add_argument('--debug', action='store_true', help='Debug mode: process only 1 run; set num_concurrency=1')
    return p.parse_args()


def _infer_dataset_and_exptype(results_json: str, run_dir: str) -> Tuple[Optional[str], Optional[str]]:
    dataset: Optional[str] = None
    exp_type: Optional[str] = None
    # 1) Try to read a tiny hint from results JSON (first prediction's 'category')
    try:
        import json
        with open(results_json, 'r', encoding='utf-8') as f:
            data = json.load(f)
        # take first value list and first item
        for _k, v in data.items():
            if isinstance(v, list) and v:
                item = v[0]
                if isinstance(item, dict):
                    cat = item.get('category')
                    if isinstance(cat, str) and cat:
                        dataset = cat
                break
    except Exception:
        pass

    # 2) Infer experiment_type from run_dir naming (…_learned_… / …_oracle_… / …_barebone_…)
    name = os.path.basename(run_dir).lower()
    if 'learned' in name:
        exp_type = 'learned'
    elif 'oracle' in name:
        exp_type = 'oracle'
    elif 'barebone' in name:
        exp_type = 'barebone'
    
    # IMPORTANT: Do NOT force dataset=DSL based on exp_type tokens in the run name.
    # Some ProofNet runs include method labels like "..._formalized-structure_learned_..." in their folder name.
    # We only use the JSON 'category' field to infer dataset when available.
    # If JSON didn't provide it (dataset is None), we leave it as None and let CLI args or user override decide.

    return dataset, exp_type


def run_checker_for(run_dir: str, results_json: str, args: argparse.Namespace) -> int:
    inferred_dataset, inferred_exptype = _infer_dataset_and_exptype(results_json, run_dir)
    # Decide where to place outputs: default to the run directory; override when output_root is provided
    base_out_dir = run_dir
    if getattr(args, 'output_root', None):
        base_out_dir = os.path.join(args.output_root, os.path.basename(run_dir.rstrip(os.sep)))
    cmd = [
        sys.executable, '-m', 'afc.proofnet.proofnet_checker', 'run',
        '--input', results_json,
        '--root_dir', args.root_dir,
        '--base_output_dir', base_out_dir,
        '--eval_set', 'proofnet',
        '--num_concurrency', str(args.num_concurrency),
        '--timeout', str(args.timeout),
        '--lean_version', args.lean_version,
        '--stat_mode', args.stat_mode,
    ]
    # Pass dataset/experiment_type through to ensure relations are properly injected
    dataset = args.dataset or inferred_dataset
    exptype = args.experiment_type or inferred_exptype
    if dataset:
        cmd += ['--dataset', dataset]
    # Only pass experiment_mode when dataset is DSL (relations injection is DSL-only)
    if exptype and (dataset or '').upper() == 'DSL':
        cmd += ['--experiment_mode', exptype]
    elif exptype and (dataset or '').upper() != 'DSL':
        print(f"[meta] Ignoring experiment_mode='{exptype}' for non-DSL dataset '{dataset}'.")

    if dataset or exptype:
        print(f"[meta] Inferred meta for {os.path.basename(run_dir)} -> dataset={dataset or 'N/A'}, experiment_type={exptype or 'N/A'}")
    if args.mathlib_root:
        cmd += ['--mathlib_root', args.mathlib_root]
    if args.repl_root:
        cmd += ['--repl_root', args.repl_root]
    if args.strategies:
        cmd += ['--strategies'] + list(args.strategies)
    # Pass optional task limit through to the checker (if provided)
    if getattr(args, 'limit_tasks', None) is not None:
        cmd += ['--limit_tasks', str(int(args.limit_tasks))]
    if 'llm' in args.strategies:
        # Use fixed endpoint and model; token is read from environment by the checker
        cmd += ['--equiv_url', LLM_URL_DEFAULT]
        cmd += ['--equiv_model', LLM_MODEL_DEFAULT]
        cmd += [
            '--generate_queries', str(args.generate_queries),
            '--num_samples', str(args.num_samples),
            '--max_tokens', str(args.max_tokens),
            '--temperature', str(args.temperature),
        ]
    # Pass ground-truth CSV for DSL to help checker fill header/formal
    gt_csv = args.gt_csv
    # Auto-pick a reasonable ground-truth CSV if not provided
    ds_upper = (dataset or '').upper() if dataset else None
    if ds_upper == 'DSL':
        candidate = os.path.join(args.root_dir, 'data', 'proofnet_dsl', 'ProofNet-Lean4_proof_dsl.csv')
        if os.path.isfile(candidate):
            gt_csv = candidate
    if gt_csv:
        cmd += ['--gt_csv', gt_csv]
    print(f"🔎 Checking: {results_json}")
    return subprocess.call(cmd)


def main() -> int:
    args = parse_args()
    root = os.path.abspath(args.root)
    if not os.path.isdir(root):
        print(f"[!] Root not found: {root}")
        return 1

    # Apply debug overrides
    if args.debug:
        print('[debug] Enabling debug mode: num_concurrency=1, limit to first run folder')
        args.num_concurrency = 1

    for i, (run_dir, results_json) in enumerate(iter_run_folders(root)):
        run_checker_for(run_dir, results_json, args)


if __name__ == '__main__':
    raise SystemExit(main())
