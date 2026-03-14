from __future__ import annotations

import json
import os.path as osp
import re
from typing import Dict, List, Optional, Tuple

from ...utils import merge_lean_sections
from .constants import DEFAULT_HEADER, THM_CODE_PATTERN
from lean_interact import AutoLeanServer, Command
from lean_interact.interface import CommandResponse, LeanError, Pos, message_intersects_code
from lean_interact.utils import indent_code


def load_samples_index(dataset_root: str, eval_set: str) -> Dict[str, dict]:
    benchmark = osp.join(dataset_root, eval_set, "benchmark.jsonl")
    index: Dict[str, dict] = {}
    try:
        with open(benchmark, "r", encoding="utf-8") as f:
            for line in f:
                sample = json.loads(line)
                index[sample["full_name"]] = sample
    except Exception:
        pass
    return index


def header_or_default(header: Optional[str], relations_snippet: str) -> str:
    merged = merge_lean_sections(DEFAULT_HEADER, header or "", relations_snippet).rstrip()
    return (merged + "\n") if merged else ""


def normalize_thm_names(gt_stmt: str, pred_stmt: str, problem_name: str) -> Tuple[str, str]:
    gt_norm = gt_stmt.replace(f"theorem {problem_name}", "theorem thm_P")
    try:
        matches_thm = list(re.finditer(THM_CODE_PATTERN, pred_stmt))
        matches_eg = list(re.finditer("example", pred_stmt))
        if len(matches_thm) == 1:
            thm_name = matches_thm[0].group().split()[1].strip()
            pred_stmt = pred_stmt.replace(f"theorem {thm_name}", "theorem thm_Q")
        elif len(matches_eg) == 1:
            pred_stmt = pred_stmt.replace("example", "theorem thm_Q")
    except Exception:
        pass
    return gt_norm, pred_stmt


def extract_exact_proof(lean_output: CommandResponse, proof_start_line: Optional[int] = None) -> Optional[str]:
    start = Pos(line=proof_start_line, column=0) if proof_start_line else None
    for message in lean_output.messages:
        if message_intersects_code(message, start, None):
            if message.severity == "error":
                return None
            if message.severity == "info" and isinstance(message.data, str) and message.data.startswith("Try this:"):
                return message.data.split("Try this:")[1].strip()
    return None


def check_proof_sub(
    server: AutoLeanServer,
    formal_code: str,
    context_env: int,
    formal_2_start_line: int,
    proof: str,
    timeout: int,
    indent_level: int = 2,
) -> Optional[str]:
    prepended = "\nintros\nsymm_saturate\n"
    try:
        lean_output = server.run(
            Command(cmd=formal_code + indent_code(prepended + proof, indent_level), env=context_env),
            timeout=timeout,
        )
        if isinstance(lean_output, LeanError):
            return None
        if proof == "sorry":
            if lean_output.lean_code_is_valid(start_pos=Pos(line=formal_2_start_line, column=0)):
                return proof
            return None

        if lean_output.lean_code_is_valid(start_pos=Pos(line=formal_2_start_line, column=0), allow_sorry=False):
            if proof == "exact?":
                return extract_exact_proof(lean_output, proof_start_line=formal_2_start_line)
            return proof
    except TimeoutError:
        pass
    except (ConnectionAbortedError, json.JSONDecodeError):
        pass
    return None
