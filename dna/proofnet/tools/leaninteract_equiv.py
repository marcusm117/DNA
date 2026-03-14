from __future__ import annotations

"""
LeanInteract-based equivalence checking utilities (PQ and QP) without any LLM.
Extracted from afc.proofnet.leaninteract_equiv and placed under tools/.
"""

import os
import json
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple


def _ensure_leaninteract_on_path(working_root: Optional[str] = None) -> None:
    import sys
    candidates = []
    if working_root:
        candidates.append(os.path.join(working_root, "LeanInteract", "src"))
    candidates.append(os.path.join(os.getcwd(), "LeanInteract", "src"))
    for p in candidates:
        if os.path.isdir(p) and p not in sys.path:
            sys.path.append(p)


def make_default_repl_config(require_mathlib: bool = True, verbose: bool = False, lean_version: Optional[str] = None):
    _ensure_leaninteract_on_path()
    from lean_interact.config import LeanREPLConfig
    if require_mathlib:
        from lean_interact.project import TempRequireProject
        project = TempRequireProject(lean_version=lean_version, require="mathlib")
        return LeanREPLConfig(project=project, verbose=verbose)
    return LeanREPLConfig(lean_version=lean_version, verbose=verbose)


@dataclass
class EquivAttempt:
    strategy: str
    proof: Optional[str]
    success: bool
    extra: Dict


class LeanInteractEquivChecker:
    def __init__(self, repl_config) -> None:
        _ensure_leaninteract_on_path()
        from lean_interact import AutoLeanServer, Command
        from lean_interact.interface import CommandResponse
        self._AutoLeanServer = AutoLeanServer
        self._Command = Command
        self._CommandResponse = CommandResponse
        self.server = self._AutoLeanServer(config=repl_config)

    @staticmethod
    def _extract_exact_proof(lean_output, proof_start_line: Optional[int] = None) -> Optional[str]:
        from lean_interact.interface import Pos, message_intersects_code
        start = Pos(line=proof_start_line, column=0) if proof_start_line is not None else None
        for message in getattr(lean_output, "messages", []):
            if message_intersects_code(message, start, None):
                if message.severity == "error":
                    return None
                if message.severity == "info" and isinstance(message.data, str) and message.data.startswith("Try this:"):
                    return message.data.split("Try this:")[1].strip()
        return None

    def _check_proof_sub(
        self,
        formal_code: str,
        context_env: int,
        formal_2_start_line: int,
        proof: str,
        timeout: int,
        indent_level: int = 2,
    ) -> Optional[str]:
        from lean_interact.interface import CommandResponse, LeanError, Pos
        from lean_interact.utils import indent_code
        prepended = "\nintros\nsymm_saturate\n"
        try:
            resp = self.server.run(
                self._Command(cmd=formal_code + indent_code(prepended + proof, indent_level), env=context_env),
                timeout=timeout,
            )
            if isinstance(resp, LeanError):
                return None
            start_pos = Pos(line=formal_2_start_line, column=0)
            if proof == "sorry":
                return proof if resp.lean_code_is_valid(start_pos=start_pos) else None
            if not resp.lean_code_is_valid(start_pos=start_pos, allow_sorry=False):
                return None
            if proof == "exact?":
                return self._extract_exact_proof(resp, proof_start_line=formal_2_start_line)
            return proof
        except TimeoutError:
            return None
        except (ConnectionAbortedError, json.JSONDecodeError):
            return None

    def _build_formals(self, code_P: str, code_Q: str) -> Tuple[str, int, str, str]:
        from lean_interact.utils import clean_last_theorem_string
        base_thm_name = "base_theorem"
        reformulated_thm_name = "reformulated_theorem"
        formal_1_code = clean_last_theorem_string(code_P, base_thm_name, add_sorry=True) + "\n\n"
        formal_2_start_line = formal_1_code.count("\n") + 1
        formal_2_code = f"{clean_last_theorem_string(code_Q, reformulated_thm_name, add_sorry=False)} := by"
        return formal_1_code + formal_2_code, formal_2_start_line, base_thm_name, reformulated_thm_name

    @staticmethod
    def _prove_all(tactics: List[str]) -> str:
        prove_independent = " ; ".join([f"(all_goals try {t})" for t in tactics])
        prove_combined = "all_goals (" + " ; ".join([f"(try {t})" for t in tactics]) + ")"
        return "all_goals intros\nfirst | (" + prove_independent + ") | (" + prove_combined + ")"

    def check_one_direction(
        self,
        header: str,
        code_P: str,
        code_Q: str,
        timeout: int = 60,
    ) -> Tuple[bool, List[EquivAttempt]]:
        from lean_interact.interface import CommandResponse
        from lean_interact.utils import split_conclusion, indent_code
        ctx_resp = self.server.run(self._Command(cmd=header), add_to_session_cache=True)
        assert isinstance(ctx_resp, CommandResponse)
        context_env = ctx_resp.env
        try:
            formal_code, formal_2_start_line, base_thm_name, _ = self._build_formals(code_P, code_Q)
        except Exception:
            return False, [EquivAttempt("build", None, False, {"error": "invalid theorems"})]
        if self._check_proof_sub(formal_code, context_env, formal_2_start_line, "sorry", timeout) is None:
            return False, [EquivAttempt("typecheck", None, False, {"error": "ill-typed"})]
        attempts: List[EquivAttempt] = []
        proof_exact = self._check_proof_sub(formal_code, context_env, formal_2_start_line, "exact?", timeout)
        if proof_exact and base_thm_name in proof_exact:
            attempts.append(EquivAttempt("exact", proof_exact, True, {}))
            return True, attempts
        attempts.append(EquivAttempt("exact", proof_exact, False, {}))
        solver_tactics_apply = ["tauto", "simp_all_arith!", "noncomm_ring", "exact?"]
        solver_tactics_have = ["tauto", "simp_all_arith!", "exact? using this"]
        proof_all_apply = self._prove_all(solver_tactics_apply)
        proof_all_have = self._prove_all(solver_tactics_have)
        proof_apply = self._check_proof_sub(formal_code, context_env, formal_2_start_line, f"apply {base_thm_name}\n" + proof_all_apply, timeout)
        if proof_apply:
            attempts.append(EquivAttempt("apply", proof_apply, True, {}))
            return True, attempts
        attempts.append(EquivAttempt("apply", proof_apply, False, {}))
        provable_without_have = False
        try:
            resp = self.server.run(self._Command(cmd=formal_code + proof_all_have, env=context_env), timeout=timeout)
            if isinstance(resp, CommandResponse):
                provable_without_have = resp.lean_code_is_valid(allow_sorry=False)
        except Exception:
            pass
        if not provable_without_have:
            idx_conclusion = split_conclusion(formal_code)
            if idx_conclusion:
                idx_end_conclusion = formal_code.rfind(":=")
                conclusion = formal_code[idx_conclusion:idx_end_conclusion].strip()
                have_stmt_proof = (
                    f"have {conclusion} := by\n" + indent_code(f"apply_rules [{base_thm_name}]\n" + proof_all_apply, 2) + "\n"
                )
                proof_have = self._check_proof_sub(formal_code, context_env, formal_2_start_line, have_stmt_proof + proof_all_have, timeout)
                if proof_have:
                    attempts.append(EquivAttempt("have", proof_have, True, {}))
                    return True, attempts
                attempts.append(EquivAttempt("have", proof_have, False, {}))
        for max_step in range(0, 5):
            proof_convert = self._check_proof_sub(
                formal_code,
                context_env,
                formal_2_start_line,
                f"convert (config := .unfoldSameFun) {base_thm_name} using {max_step}\n" + proof_all_apply,
                timeout,
            )
            if proof_convert:
                attempts.append(EquivAttempt(f"convert_using_{max_step}", proof_convert, True, {}))
                return True, attempts
            attempts.append(EquivAttempt(f"convert_using_{max_step}", proof_convert, False, {}))
        return False, attempts

    def check_bi_equiv(
        self,
        header: str,
        code_P: str,
        code_Q: str,
        timeout: int = 60,
    ) -> Tuple[bool, Dict[str, List[EquivAttempt]]]:
        ok_PQ, att_PQ = self.check_one_direction(header, code_P, code_Q, timeout=timeout)
        if not ok_PQ:
            return False, {"PQ": att_PQ, "QP": []}
        ok_QP, att_QP = self.check_one_direction(header, code_Q, code_P, timeout=timeout)
        return ok_PQ and ok_QP, {"PQ": att_PQ, "QP": att_QP}

