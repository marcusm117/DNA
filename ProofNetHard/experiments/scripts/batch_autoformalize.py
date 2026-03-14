from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from datetime import datetime
from pathlib import Path
from typing import List, Dict, Any, Optional
from dotenv import load_dotenv

# load dataset root path and experiment root path from .env file
load_dotenv()
DATASET_ROOT = os.getenv("DATASET_ROOT")
EXPERIMENT_ROOT = os.getenv("EXPERIMENT_ROOT")


# Generate timestamp for this batch run
BATCH_TIMESTAMP = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
BATCH_DIR = Path(f'outputs/exeperiments_{BATCH_TIMESTAMP}')


TARGET_COMBOS: List[tuple[str, str]] = [
    # ("oracle", "1_direct"),
    ("oracle", "4_formalized-structure"),
    # ("learned", "4_formalized-structure"),
    # ("learned", "1_direct"),
    # ("barebone", "4_formalized-structure"),
    # ("barebone", "1_direct"),
]

# Models to run; edit this list to include all target models
MODELS: List[str] = [
    "gpt-4.1-mini-2025-04-14",
    # "gpt-4.1-2025-04-14",
    # "gpt-5-mini-2025-08-07",
    # "gpt-5-2025-08-07",
    # "AI-MO/Kimina-Autoformalizer-7B",
    # "huawei-ai4math/Mathesis-Autoformalizer",
    # "huawei-ai4math/Mathesis-Autoformalizer-HPO",
    # "anthropic/claude-sonnet-4",
    # "anthropic/claude-sonnet-4-thinking",
    # "qwen/qwen3-14b",
    # "qwen/qwen3-32b",
    # "qwen/qwen3-235b-a22b-2507",
    # "qwen/qwen3-14b-thinking",
    # "qwen/qwen3-32b-thinking"
    # "qwen/qwen3-235b-a22b-thinking-2507",
]

# Thinking toggle applied to all runs (for supported models)
USE_THINKING: bool = False

# Pipeline/checker configs are generated on the fly and written here
# No longer need configuration file paths since we pass configs directly
NUM_PROCESSES = 100 # Number of parallel processes for autoformalization pipeline
AYSNC_PROCESSES = 1  # Number of async tasks for autoformalization pipeline
LIMIT_PROBLEMS = 0
DATA_SET = "DSL"
ONE_SHOT_EXAMPLE = "Cambridge-Tripos.exercise_2022_IB_3_II_13G_a_i"

# Configuration function removed - configs are now created directly in main()


def run_single(
    model: str,
    method: str,
    config: dict,
    thinking: bool,
    limit: Optional[int],
    num_run: Optional[int],
    experiment_type: str,
) -> None:

    # 1) Run the autoformalization pipeline
    pipe_cmd = [sys.executable, 'pipeline/autoformalize_pipeline.py']

    pipe_cmd += ['--dataset', config.get('dataset', 'DSL')]
    pipe_cmd += ['--method', method]
    pipe_cmd += ['--model', model]
    pipe_cmd += ['--experiment_type', experiment_type]
    pipe_cmd += ['--result_dir_name', str(BATCH_DIR)]

    if 'reasoning' in config:
        pipe_cmd += ['--reasoning', config['reasoning']]
    if 'num_query' in config:
        pipe_cmd += ['--num_query', str(config['num_query'])]
    if 'num_examples' in config:
        pipe_cmd += ['--num_examples', str(config['num_examples'])]
    if 'example_choices' in config and config['example_choices'] != ['none']:
        pipe_cmd += ['--example_choices'] + config['example_choices']
    if 'example_format' in config:
        pipe_cmd += ['--example_format', config['example_format']]
    if 'cot_for_reasoning_models' in config:
        pipe_cmd += ['--cot_for_reasoning_models', config['cot_for_reasoning_models']]
    if 'num_process' in config:
        pipe_cmd += ['--num_process', str(config['num_process'])]
    if 'temperature' in config:
        pipe_cmd += ['--temperature', str(config['temperature'])]
    if 'num_async' in config:
        pipe_cmd += ['--num_async', str(config['num_async'])]
    if 'enable_caching' in config and config['enable_caching']:
        pipe_cmd += ['--enable_caching']
    if 'dataset_root' in config and config['dataset_root']:
        pipe_cmd += ['--dataset_root', config['dataset_root']]
    if 'save_detailed_response' in config and config['save_detailed_response']:
        pipe_cmd += ['--save_detailed_response']
    if config.get('root_dir'):
        pipe_cmd += ['--root_dir', config['root_dir']]

    if thinking:
        pipe_cmd += ['--openai_reasoning_effort', 'high']
    if limit is not None:
        pipe_cmd += ['--limit', str(limit)]
    if num_run is not None:
        pipe_cmd += ['--num_run', str(num_run)]

    subprocess.run(pipe_cmd, check=True)

    # Checker is decoupled; run experiments only in this script.
    return


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Batch launcher for autoformalization experiments")
    # Single debug switch as the only CLI control; all other knobs live in base_config
    parser.add_argument("--debug", action="store_true", help="Run a minimal debug pass (single process/run/limit)")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    # Create batch directory
    BATCH_DIR.mkdir(parents=True, exist_ok=True)
    print(f"🚀 Starting batch autoformalization run with timestamp: {BATCH_TIMESTAMP}")
    print(f"📁 All results will be saved in: {BATCH_DIR}")

    # Derive concurrency settings (debug => all 1)
    if args.debug:
        print("🧪 Debug mode ON: setting num_process=1, num_async=1, limit=1, num_run=1")
        num_processes = 1
        async_processes = 1
        limit_problems = 1
        run_num = 1
    else:
        num_processes = NUM_PROCESSES
        async_processes = AYSNC_PROCESSES
        limit_problems = LIMIT_PROBLEMS
        run_num = 5

    # Create config dictionaries directly
    base_config = {
        "dataset": DATA_SET,
        "dataset_root":  DATASET_ROOT,
        "reasoning": "text-only",
        "num_query": 5,
        "num_examples": 0,
        "example_choices": ["none"],
        "example_format": "content",
        "cot_for_reasoning_models": "full",
        "num_process": num_processes,
        "num_async": async_processes,
        "enable_caching": True,
        "temperature": 0.2,
        "num_run": run_num,
        "save_detailed_response": False,
        "limit": limit_problems,
        "root_dir": EXPERIMENT_ROOT,
        # Checker is decoupled; all checker_* config removed.
    }

    # 1-shot ProofNet config
    proofnet_1shot_config = {
        **base_config,
        "dataset": "DSL",
        "num_examples": 1,
        "example_choices": [ONE_SHOT_EXAMPLE],
    }

    models = MODELS
    thinking = USE_THINKING

    # Run both configurations
    configs = [
        ("ProofNet_1shot", proofnet_1shot_config),
        # ("DSL_0shot", base_config)
    ]
    # Iterate over requested combinations only, for both 0-shot and 1-shot configs
    for experiment_type, method in TARGET_COMBOS:
        for config_name, config in configs:
            for model in models:
                print(f"== Config: {config_name} | exp: {experiment_type} | method: {method} | model: {model} (thinking={thinking}) ==")
                run_single(
                    model,
                    method,
                    config,
                    thinking,
                    limit_problems,  # limit problems (debug => 1)
                    run_num,         # num_run (debug => 1)
                    experiment_type,
                )

    return 0


if __name__ == '__main__':
    raise SystemExit(main())
