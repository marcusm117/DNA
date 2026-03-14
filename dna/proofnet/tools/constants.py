from __future__ import annotations

# Re-export prior constants module contents if needed. Keep placeholders minimal.

# Import patterns for code blocks and theorem declarations
import re

CODEBLOCK_PATTERN = re.compile(r"```(?:lean)?\n(.*?)```", re.DOTALL)
THM_CODE_PATTERN = re.compile(r"\btheorem\s+\w+\b")

# Whitelists and blacklists used by LLM proof extraction
BANNED_TOKENS = ["sorry", "admit", "Admitted"]
ALLOWED_TACTICS = [
    "simp", "simp_all", "simp_all_arith!", "tauto", "ring", "noncomm_ring", "aesop", "exact?",
]

# Default Lean header used by checker
DEFAULT_HEADER = """
import Mathlib

open Real Complex Filter Function Metric Finset
open scoped BigOperators Topology

set_option maxHeartbeats 200000
set_option maxRecDepth 20000
noncomputable section
""".strip()

# Prompt template for LLM equivalence proving
EQUIV_PROVING_PROMPT_TEMPLATE = """
You are given a Lean header and two theorems thm_P (ground truth) and thm_Q (prediction).
Prove the equivalence between thm_P and thm_Q by supplying a Lean proof for thm_Q
using thm_P. Use only tactics from {ALLOWED_TACTICS} and do not include disallowed tokens.
Return exactly one Markdown code block with the Lean proof body.
{autoformalization_result}
""".strip()

