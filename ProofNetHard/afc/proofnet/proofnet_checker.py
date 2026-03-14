from __future__ import annotations

import os
import sys
import asyncio
import json
import re
from typing import Dict, Optional, Tuple, List
import signal
import contextlib

from joblib import Parallel, delayed
from tqdm.auto import tqdm

from ..utils import read_text_if_exists, ensure_lean_tools_on_path, extract_first_code_block
from .tools.constants import (
    CODEBLOCK_PATTERN as _CODEBLOCK_PATTERN,
    BANNED_TOKENS as _BANNED_TOKENS,
    ALLOWED_TACTICS as _ALLOWED_TACTICS,
    THM_CODE_PATTERN as _THM_CODE_PATTERN,
    DEFAULT_HEADER as _DEFAULT_HEADER,
    EQUIV_PROVING_PROMPT_TEMPLATE as _PROMPT,
)
from .tools.utils import (
    header_or_default as pn_header_or_default,
    normalize_thm_names as pn_normalize_thm_names,
    check_proof_sub as pn_check_proof_sub,
)
from .tools.analysis import EquivalenceResultsManager



from lean_interact import AutoLeanServer, Command, LeanREPLConfig
from lean_interact.interface import CommandResponse
from lean_interact.project import TempRequireProject
from lean_interact.utils import clean_last_theorem_string, indent_code, split_conclusion

from .common.constants import INIT_WAIT_TIME
from .common.dataclasses import Environment
from .common.repl import REPL
from .tools.llm_utils import build_async_text_generator

# Prevent debugpy from attempting to attach to joblib subprocesses when running under a debugger.
# This avoids noisy "Error patching args" messages in some debugger integrations.
os.environ.setdefault("PYDEVD_DISABLE_SUBPROCESS_DEBUG", "1")
os.environ.setdefault("PYDEVD_DISABLE_FILE_VALIDATION", "1")



def add_newlines_to_full_theorem(theorem: str) -> str:
    """Insert blank lines after key Lean header statements.

    Ensures the tokens `import Mathlib`, `open …`, and `open scoped …` are each
    followed by two newline characters, even if the input is a flat single-line
    string. Additional occurrences of these statements are handled as well.
    """

    text = str(theorem or "")
    if not text.strip():
        return text

    break_tokens = (
        'import ',
        'open scoped ',
        'open ',
        'theorem ',
        'lemma ',
        'def ',
        'example ',
        'noncomputable ',
        'section ',
        'namespace ',
        'structure ',
        'class ',
        'inductive ',
        'instance ',
        'notation ',
        'variable ',
        'universe ',
        'axiom ',
        'constant ',
        'mutual ',
    )

    def _find_span(src: str, start: int) -> tuple[int, int]:
        idx = start
        n = len(src)
        end = idx
        while end < n:
            ch = src[end]
            if ch == '\n':
                break
            if ch.isspace():
                ws_start = end
                while end < n and src[end].isspace() and src[end] != '\n':
                    end += 1
                if end < n and src[end] == '\n':
                    end = ws_start
                    break
                if any(src.startswith(tok, end) for tok in break_tokens):
                    end = ws_start
                    break
                continue
            end += 1
        while end > idx and src[end - 1] in ' \t':
            end -= 1
        return idx, end

    def _apply_once(src: str, idx: int) -> tuple[str, int]:
        start, end = _find_span(src, idx)
        statement = src[start:end].rstrip(' \t')
        suffix = src[end:]
        suffix = suffix.lstrip(' \t')
        while suffix.startswith('\n'):
            suffix = suffix[1:]
            suffix = suffix.lstrip(' \t')
        formatted = src[:start] + statement
        if statement:
            formatted += '\n\n'
        formatted += suffix
        next_index = start + len(statement) + (2 if statement else 0)
        return formatted, next_index

    def _find_import(src: str, start: int) -> int:
        return src.find('import Mathlib', start)

    def _find_open_scoped(src: str, start: int) -> int:
        return src.find('open scoped', start)

    def _find_open(src: str, start: int) -> int:
        idx = start
        while True:
            idx = src.find('open ', idx)
            if idx == -1:
                return -1
            if src.startswith('open scoped', idx):
                idx += len('open ')
                continue
            return idx

    def _apply_keyword(src: str, finder) -> str:
        current = src
        search_start = 0
        while True:
            pos = finder(current, search_start)
            if pos == -1:
                break
            current, search_start = _apply_once(current, pos)
        return current

    text = _apply_keyword(text, _find_import)
    text = _apply_keyword(text, _find_open_scoped)
    text = _apply_keyword(text, _find_open)
    return text


def remove_imports(theorem: str) -> str:
    # remove all import statements from theorem
    if not theorem:
        return ""
    sanitized_lines = [
        line for line in str(theorem).splitlines() if not line.lstrip().startswith("import ")
    ]
    sanitized_theorem = "\n".join(sanitized_lines).strip()
    return sanitized_theorem


def separate_open_theorem(theorem: str) -> tuple[str, str]:
    """Remove Lean comments and split around the first `theorem`.

    Returns a pair (before, after) where:
    - `before` is everything before the first `theorem` (with comments removed).
    - `after` starts at the `theorem` keyword (keeps the keyword).

    If no `theorem` is found, returns (sanitized_source, "").
    """
    src = theorem or ""

    def _strip_lean_comments(s: str) -> str:
        out: list[str] = []
        n = len(s)
        i = 0
        block_depth = 0
        in_line_comment = False
        in_string = False
        while i < n:
            ch = s[i]
            nxt = s[i + 1] if i + 1 < n else ""

            if in_string:
                # Preserve string content
                out.append(ch)
                if ch == "\\":
                    # Skip escaped char
                    if i + 1 < n:
                        out.append(s[i + 1])
                        i += 2
                        continue
                if ch == '"':
                    in_string = False
                i += 1
                continue

            if in_line_comment:
                # Discard until newline, but keep the newline
                if ch == "\n":
                    out.append("\n")
                    in_line_comment = False
                i += 1
                continue

            if block_depth > 0:
                # Nested block comments /- ... -/
                if ch == "/" and nxt == "-":
                    block_depth += 1
                    i += 2
                    continue
                if ch == "-" and nxt == "/":
                    block_depth -= 1
                    i += 2
                    continue
                i += 1
                continue

            # Not in comment or string
            if ch == '"':
                in_string = True
                out.append(ch)
                i += 1
                continue
            if ch == "-" and nxt == "-":
                in_line_comment = True
                i += 2
                continue
            if ch == "/" and nxt == "-":
                block_depth = 1
                i += 2
                continue

            out.append(ch)
            i += 1
        return "".join(out)

    clean = _strip_lean_comments(src)
    m = re.search(r"\btheorem\b", clean)
    if not m:
        return clean, ""
    start = m.start()
    return clean[:start], clean[start:]


class FastEquivChecker:
    DEFAULT_TIMEOUT = 60
    RELATIONS_SNIPPET = ""

    # Parsing and prompt utilities (moved to constants module)
    CODEBLOCK_PATTERN = _CODEBLOCK_PATTERN
    BANNED_TOKENS = _BANNED_TOKENS
    ALLOWED_TACTICS = _ALLOWED_TACTICS
    THM_CODE_PATTERN = _THM_CODE_PATTERN

    DEFAULT_HEADER = _DEFAULT_HEADER

    EQUIV_PROVING_PROMPT_TEMPLATE = _PROMPT.replace('{ALLOWED_TACTICS}', '[' + ', '.join(ALLOWED_TACTICS) + ']')

    def __init__(
        self,
        *,
        args: Optional[object] = None
    ) -> None:
        """Initialize checker from args namespace or explicit keywords."""

        self.args = args

        # Roots
        self.root_dir = getattr(args, 'root_dir', '.')
        self.dataset_root = os.path.join(self.root_dir, 'data')
        self.eval_set = getattr(args, 'checker_eval_set', getattr(args, 'eval_set', 'proofnet'))
        mathlib_root_rel = getattr(args, 'checker_mathlib_root', getattr(args, 'mathlib_root', None))
        self.mathlib_root = os.path.join(self.root_dir, mathlib_root_rel) if mathlib_root_rel else None
        repl_root_rel = getattr(args, 'checker_repl_root', getattr(args, 'repl_root', None))
        self.repl_root = os.path.join(self.root_dir, repl_root_rel) if repl_root_rel else None

        # Do NOT pre-read DSL relations here; workers may differ by experiment_mode.
        # Keep a blank default; resolve per-task instead.
        self.relations_snippet = ""
        FastEquivChecker.RELATIONS_SNIPPET = ""
        base_out = getattr(args, 'checker_base_output_dir', getattr(args, 'base_output_dir', None)) if args else None
        detail_dir = getattr(args, 'detailed_logs_dir', None) if args else None
        self.results_manager = EquivalenceResultsManager(base_output_dir=base_out or self.root_dir, detailed_logs_dir=detail_dir)
    
    def _resolve_relations_snippet(self, *, experiment_mode: Optional[str], dataset: Optional[str]) -> str:
        """Resolve DSL relations content per task based on experiment mode.

        - Only applies to dataset == 'DSL'.
        - Supports explicit override via args.dsl_relations_path when provided.
        - Falls back to pipeline/instructions/dsl_instructions/Relations_*.lean
        """
        try:
            if dataset != "DSL":
                return ""
            # Explicit override if provided
            rel_override = getattr(self.args, 'dsl_relations_path', None)
            if rel_override:
                return read_text_if_exists(rel_override) or ""
            # Map by experiment_mode
            if experiment_mode not in {"oracle", "learned"}:
                return ""
            instructions_dir = os.path.join(self.root_dir, 'pipeline', 'instructions', 'dsl_instructions')
            rel_name = 'Relations_oracle.lean' if experiment_mode == 'oracle' else 'Relations_learned.lean'
            rel_path = os.path.join(instructions_dir, rel_name)
            return read_text_if_exists(rel_path) or ""
        except Exception:
            return ""


    def _parser_result_root(self) -> list[dict]:
        import glob
        results: List[dict] = []
        # Scan roots: allow override via args.fastchecker_scan_roots (list[str] or str)
        scan_roots = getattr(self.args, 'fastchecker_scan_roots', None)
        if isinstance(scan_roots, str):
            scan_roots = [scan_roots]
        if not scan_roots:
            scan_roots = [os.path.join(self.root_dir, 'outputs')]

        gt_csv = getattr(self.args, 'checker_gt_csv', None)
        dataset = getattr(self.args, 'dataset', getattr(self.args, 'checker_eval_set', self.eval_set))

        def _parse_run_folder(name: str) -> tuple[str, str, str, str]:
            # name format: <model>_<method>[_<exp>]_<shot>
            toks = name.split('_')
            if len(toks) < 3:
                return name, '', '', ''
            shot = toks[-1]
            maybe_exp = toks[-2]
            if maybe_exp in {'barebone', 'learned', 'oracle'}:
                method = toks[-3] if len(toks) >= 3 else ''
                exp = maybe_exp
                model = '_'.join(toks[:-3]) if len(toks) >= 3 else ''
            else:
                method = maybe_exp
                exp = ''
                model = '_'.join(toks[:-2]) if len(toks) >= 2 else ''
            return model, method, exp, shot

        from pathlib import Path
        seen_dirs = set()
        
        
        for root in scan_roots:
            pattern = os.path.join(str(root), '**', '*_result.json')
            paths = glob.glob(pattern, recursive=False)
            for path in paths:
                try:
                    path = str(path)
                    run_dir = os.path.dirname(path)
                    if run_dir in seen_dirs:
                        continue
                    seen_dirs.add(run_dir)
                    run_folder_name = os.path.basename(run_dir)
                    model, method, exp_mode, shot = _parse_run_folder(run_folder_name)
                    # Load JSON
                    with open(path, 'r', encoding='utf-8') as f:
                        results_obj = json.load(f)
                    results.append({
                        'model': model,
                        'method': method,
                        'experiment_mode': exp_mode,
                        'dataset': dataset,
                        'autoformalization_result': results_obj,
                        'run_dir': run_dir,
                        'run_key': run_dir,
                        'gt_csv': gt_csv,
                    })
                except Exception:
                    continue

        if not results and not getattr(self.args, 'checker_quiet', False):
            print('[fastchecker] No *_result.json found, please check outputs/ or fastchecker_scan_roots configuration')
        return results

    # 任务构建：将多个结果源展开为统一的工作单元
    def _construct_tasks(self, args):
        # Load results object
        tasks: list[tuple[dict, str, int, dict, dict, str, str]] = []
        autoformalization_results = self._parser_result_root()
        for result in autoformalization_results:
            results_obj = result["autoformalization_result"]
            # try:
            #     if not getattr(self.args, 'checker_quiet', False):
            #         n_keys = len(results_obj) if isinstance(results_obj, dict) else 0
            #         print(f"[checker] Loaded results (problems={n_keys})")
            # except Exception:
            #     pass

            # Ensure Lean tools are in PATH for worker subprocesses
            ensure_lean_tools_on_path(self.root_dir)

            # Normalize predictions into a list per problem
            def _norm_preds(p):
                if isinstance(p, list):
                    return p
                if isinstance(p, dict):
                    return [p]
                return []
            
            # Optionally load ground-truth CSV (DSL) once into a map
            gt_map = None
            gt_csv = result.get('gt_csv') or getattr(self.args, 'checker_gt_csv', None)
            if gt_csv and os.path.isfile(gt_csv):
                try:
                    import csv
                    gt_map = {}
                    with open(gt_csv, 'r', encoding='utf-8') as f:
                        reader = csv.DictReader(f)
                        for row in reader:
                            key = row.get('full_name') or row.get('problem_name') or row.get('label')
                            if not key:
                                continue
                            gt_map[key] = {
                                "formal_stmt": row.get('formal_stmt') or row.get('gt_formal_stmt') or row.get('formal_stmt_gt') or "",
                                "header_wo_helper": row.get('header_wo_helper') or "",
                                "header": row.get('header') or "",
                            }
                except Exception:
                    gt_map = None

            def _build_sample_from_sources(full_name: str, pred: dict, gt_map: dict | None) -> dict:
                """Construct a minimal sample for checker workers from GT map or pred payload.

                Fields: problem_name, formal_stmt (ground truth), header_wo_helper/header (optional)
                """
                sample: dict = {"problem_name": full_name}

                # Prefer ground-truth from provided CSV map
                if gt_map and full_name in gt_map:
                    gt_entry = gt_map[full_name]
                    gt_stmt = gt_entry.get("formal_stmt")
                    if isinstance(gt_stmt, str) and gt_stmt.strip():
                        sample["formal_stmt"] = gt_stmt
                    hdr_wo = gt_entry.get("header_wo_helper")
                    if isinstance(hdr_wo, str) and hdr_wo.strip():
                        sample["header_wo_helper"] = hdr_wo
                    hdr = gt_entry.get("header")
                    if isinstance(hdr, str) and hdr.strip():
                        sample["header"] = hdr

                # Fallbacks from prediction payload when GT missing
                if "formal_stmt" not in sample:
                    for k in ("formal_statement_ground_truth", "gt_formal_stmt", "formal_stmt_gt", "formal_stmt"):
                        v = pred.get(k)
                        if isinstance(v, str) and v.strip():
                            sample["formal_stmt"] = v
                            break
                if "header_wo_helper" not in sample and "header" not in sample:
                    for k in ("header_wo_helper", "header"):
                        hv = pred.get(k)
                        if isinstance(hv, str) and hv.strip():
                            sample[k] = hv
                            break

                            # Normalize ground-truth theorem name to `thm_P` to avoid collisions
                try:
                    gt_stmt = sample.get("formal_stmt")
                    if isinstance(gt_stmt, str) and gt_stmt.strip():
                        sample["formal_stmt"] = gt_stmt if "theorem thm_P" in gt_stmt else clean_last_theorem_string(gt_stmt, "thm_P", add_sorry=False)
                except Exception:
                    pass

                return sample

            # Strategies to apply per task
            strategies = getattr(self.args, 'checker_strategies', None) or []
            strategies = [str(s).strip().lower() for s in strategies if isinstance(s, str)]
            strategies = [s for s in strategies if s in {"beq_plus", "llm"}]
            if not strategies:
                strategies = ["beq_plus"]

            # Build minimal tasks per prediction × strategy × direction
            # Task tuple: (run_meta, full_name, pred_idx, sample, pred, method, direction)
            
            empty_pred_problems = 0
            for full_name, preds in results_obj.items():
                preds_list = _norm_preds(preds)
                if not preds_list:
                    empty_pred_problems += 1
                    continue
                for pred_idx, pred in enumerate(preds_list):
                    sample = _build_sample_from_sources(full_name, pred, gt_map)
                    for method in strategies:
                        for direction in ("pq", "qp"):
                            run_meta = {
                                'run_key': result.get('run_key') or result.get('run_dir'),
                                'run_dir': result.get('run_dir'),
                                'model': result.get('model'),
                                'method': result.get('method'),
                                'experiment_mode': result.get('experiment_mode'),
                                'dataset': result.get('dataset'),
                            }
                            tasks.append((run_meta, full_name, pred_idx, sample, pred, method, direction))
        return tasks
    # ---------------- public API ----------------
    def run(
        self,
        output_path: Optional[str] = None,
    ) -> Dict[str, list]:

        tasks = self._construct_tasks(self.args)

        # Optional: debug limit on total tasks created
        try:
            limit = int(getattr(self.args, 'checker_limit_tasks', 0) or 0)
        except Exception:
            limit = 0
        if limit > 0 and len(tasks) > limit:
            tasks = tasks[:limit]
            if not getattr(self.args, 'checker_quiet', False):
                print(f"[debug] Limiting tasks to first {limit}")

        # 简要统计输出
        if not getattr(self.args, 'checker_quiet', False):
            print(f"[checker] Built tasks: total={len(tasks)}")

        # Run unified worker in parallel
        jobs_val = getattr(self.args, 'checker_num_concurrency', 1)
        effective_jobs = int(jobs_val) if isinstance(jobs_val, int) else 1
        show_progress = bool(getattr(self.args, 'checker_progress', True))

        def _call(run_meta, full_name, pred_idx, sample, pred, method, direction):
            return self._job_worker_task(run_meta, full_name, pred_idx, sample, pred, method, direction)

        if effective_jobs <= 1:
            results = []
            iterator = tqdm(tasks, total=len(tasks), desc="Equiv unified", disable=not show_progress)
            for run_meta, full_name, pred_idx, sample, pred, method, direction in iterator:
                results.append(_call(run_meta, full_name, pred_idx, sample, pred, method, direction))
        else:
            # Provide a tqdm progress bar for joblib.Parallel without external deps.
            from contextlib import contextmanager
            from joblib import parallel as _jl_parallel

            @contextmanager
            def _tqdm_joblib(tqdm_object):
                class _TqdmBatchCallback(_jl_parallel.BatchCompletionCallBack):
                    def __init__(self, *args, **kwargs):
                        super().__init__(*args, **kwargs)
                        self.tqdm_object = tqdm_object

                    def __call__(self, *args, **kwargs):
                        try:
                            self.tqdm_object.update(n=self.batch_size)
                        except Exception:
                            pass
                        return super().__call__(*args, **kwargs)

                old_cb = _jl_parallel.BatchCompletionCallBack
                _jl_parallel.BatchCompletionCallBack = _TqdmBatchCallback
                try:
                    yield tqdm_object
                finally:
                    _jl_parallel.BatchCompletionCallBack = old_cb
                    try:
                        tqdm_object.close()
                    except Exception:
                        pass

            parallel = Parallel(
                n_jobs=effective_jobs,
                prefer="processes",
                backend="loky",
                batch_size="auto",
                pre_dispatch="2*n_jobs",
            )
            if show_progress:
                with _tqdm_joblib(tqdm(total=len(tasks), desc="Equiv unified", disable=not show_progress)):
                    results = parallel(
                        delayed(_call)(run_meta, full_name, pred_idx, sample, pred, method, direction)
                        for (run_meta, full_name, pred_idx, sample, pred, method, direction) in tasks
                    )
            else:
                results = parallel(
                    delayed(_call)(run_meta, full_name, pred_idx, sample, pred, method, direction)
                    for (run_meta, full_name, pred_idx, sample, pred, method, direction) in tasks
                )

        # Merge worker-returned records into per-run views and global view
        per_run_views: dict[str, dict] = {}  # run_key -> {'beq': {...}, 'generate': {...}}
        run_meta_map: dict[str, dict] = {}

        def _update_view(view: dict, rec: dict) -> None:
            # Mirror EquivalenceResultsManager.record_single_direction_result logic into a provided view
            problem_id = rec.get('problem_id')
            pred_idx = int(rec.get('pred_idx', 0))
            strategy = str(rec.get('strategy', 'beq_plus')).lower()
            direction = str(rec.get('direction', 'pq')).lower()
            ok = bool(rec.get('ok', False))
            info = rec.get('info')
            pred_payload = rec.get('pred_payload')
            method_key = 'generate' if strategy == 'llm' else 'beq'
            method_view = view.setdefault(method_key, {})
            plist = method_view.setdefault(problem_id, [])
            while len(plist) <= pred_idx:
                plist.append({})
            entry = plist[pred_idx] or {}
            if isinstance(pred_payload, dict):
                for k, v in pred_payload.items():
                    if k not in entry:
                        entry[k] = v
            entry.setdefault('problem_name', problem_id)
            entry['pred_idx'] = pred_idx
            entry.setdefault('equivcheck_results', {})
            entry.setdefault('strategy_results', {})
            sr = entry['strategy_results'].setdefault('llm' if strategy == 'llm' else 'beq_plus', {})
            if direction == 'pq':
                sr['pq_ok'] = ok
                if info is not None:
                    sr['result_PQ'] = info
            else:
                sr['qp_ok'] = ok
                if info is not None:
                    sr['result_QP'] = info
            # Optional compile_ok from worker (mainly for llm strategy)
            if 'compile_ok' in rec:
                try:
                    sr['compile_ok'] = bool(rec.get('compile_ok'))
                except Exception:
                    pass
            # Write legacy-compatible typecheck_result using our compile_ok if available
            if 'compile_ok' in sr:
                try:
                    entry['typecheck_result'] = {'is_success': bool(sr.get('compile_ok'))}
                except Exception:
                    pass
            tag = 'llm' if strategy == 'llm' else 'beq_plus'
            pq_ok = bool(sr.get('pq_ok', False))
            qp_ok = bool(sr.get('qp_ok', False))
            entry['equivcheck_results'][tag] = {'is_success': bool(pq_ok and qp_ok)}
            plist[pred_idx] = entry

        for r in results or []:
            rec = r.get('record') if isinstance(r, dict) else None
            if not isinstance(rec, dict):
                continue
            # Global aggregation (in-memory only; no per-task log writes)
            try:
                self.results_manager.record_single_direction_result(**rec)
            except Exception:
                pass
            # Per-run aggregation
            run_key = rec.get('run_key')
            if not run_key:
                continue
            rv = per_run_views.setdefault(run_key, {})
            _update_view(rv, rec)
            # Track meta for output paths
            if run_key not in run_meta_map:
                run_meta_map[run_key] = {
                    'run_dir': rec.get('run_dir'),
                    'model': rec.get('model'),
                    'method': rec.get('method'),
                    'experiment_mode': rec.get('experiment_mode'),
                    'dataset': rec.get('dataset'),
                }

        # Write per-run outputs back to their folders
        for run_key, views in per_run_views.items():
            meta = run_meta_map.get(run_key, {})
            out_dir = meta.get('run_dir') or run_key
            mgr = EquivalenceResultsManager(base_output_dir=out_dir, detailed_logs_dir=None)
            beq_view = views.get('beq', {})
            gen_view = views.get('generate', {})
            save_paths = {}
            if beq_view:
                save_paths['beq'] = mgr.save_method_results(method='beq_plus', checked=beq_view, output_path=None, tag='beq')
                mgr.write_per_method_summary(method='beq_plus', results=beq_view, tag='beq', stat_mode=getattr(self.args, 'checker_stat_mode', 'per_problem'))
            if gen_view:
                save_paths['generate'] = mgr.save_method_results(method='llm', checked=gen_view, output_path=None, tag='generate')
                mgr.write_per_method_summary(method='llm', results=gen_view, tag='generate', stat_mode=getattr(self.args, 'checker_stat_mode', 'per_problem'))
            aggregate = {}
            if beq_view:
                aggregate['beq'] = beq_view
            if gen_view:
                aggregate['generate'] = gen_view
            if aggregate:
                mgr.write_merged_summaries_from_aggregate(aggregate=aggregate, save_paths=save_paths, default_out_dir=out_dir, stat_mode=getattr(self.args, 'checker_stat_mode', 'per_problem'))

        # Generate top-level summary tables (Markdown + CSV) under scan roots
        try:
            scan_roots = getattr(self.args, 'fastchecker_scan_roots', None)
            if isinstance(scan_roots, str):
                scan_roots = [scan_roots]
            if not scan_roots:
                scan_roots = [os.path.join(self.root_dir, 'outputs')]
            for base in scan_roots:
                if os.path.isdir(base):
                    EquivalenceResultsManager.write_summary_tables(base_dir=base, mode='composite', metric='acc_likelybeq', write_pdf=False)
        except Exception:
            pass

        # Return basic status for caller
        return {'status': 'ok', 'runs': len(per_run_views)}


    @staticmethod
    def _beq_single_direction(
        *,
        base_thm: str,  # we want to prove reform_thm assuming base_thm
        reform_thm: str,
        src_header: str,
        repl_config: LeanREPLConfig,
        timeout_per_proof: int,
        verbose: bool = False,
    ) -> bool:

        server = AutoLeanServer(config=repl_config)
        context_run = server.run(Command(cmd=src_header), add_to_session_cache=True)
        assert isinstance(context_run, CommandResponse)
        context_env = context_run.env

        base_thm_name = "base_theorem"
        reformulated_thm_name = "reformulated_theorem"

        def prove_all(tactics: list[str]) -> str:
            prove_independent = " ; ".join([f"(all_goals try {t})" for t in tactics])
            prove_combined = "all_goals (" + " ; ".join([f"(try {t})" for t in tactics]) + ")"
            return "all_goals intros\nfirst | (" + prove_independent + ") | (" + prove_combined + ")"

        # solver_tactics_apply = ["tauto", "simp_all_arith!", "noncomm_ring", "exact?", "aesop"]
        # solver_tactics_have = ["tauto", "simp_all_arith!", "exact? using this", "aesop"]
        solver_tactics_apply = ["tauto", "simp_all_arith!", "noncomm_ring", "exact?"]
        solver_tactics_have = ["tauto", "simp_all_arith!", "exact? using this"]
        proof_all_apply = prove_all(solver_tactics_apply)
        proof_all_have = prove_all(solver_tactics_have)

        try:
            formal_1_code = clean_last_theorem_string(base_thm, base_thm_name, add_sorry=True) + "\n\n"
            formal_2_start_line = formal_1_code.count("\n") + 1
            formal_2_code = f"{clean_last_theorem_string(reform_thm, reformulated_thm_name, add_sorry=False)} := by"
        except ValueError:
            if verbose:
                pass
            return False

        formal_code = formal_1_code + formal_2_code
        if pn_check_proof_sub(server, formal_code, context_env, formal_2_start_line, "sorry", timeout_per_proof) is None:
            if verbose:
                pass
            return False

        # 1. exact?
        proof_exact = pn_check_proof_sub(server, formal_code, context_env, formal_2_start_line, "exact?", timeout_per_proof)
        if proof_exact and "base_theorem" in proof_exact:
            return True

        # 2. apply base theorem
        proof_apply = pn_check_proof_sub(
            server,
            formal_code,
            context_env,
            formal_2_start_line,
            f"apply {base_thm_name}\n" + proof_all_apply,
            timeout_per_proof,
        )
        if proof_apply:
            return True

        # 3. have base conclusion and try
        provable_without_have = False
        try:
            res_without_have = server.run(Command(cmd=formal_code + proof_all_have, env=context_env), timeout=timeout_per_proof)
            if isinstance(res_without_have, CommandResponse):
                provable_without_have = res_without_have.lean_code_is_valid(allow_sorry=False)
        except TimeoutError:
            pass
        except (ConnectionAbortedError, json.JSONDecodeError):
            pass

        if not provable_without_have:
            idx_conclusion = split_conclusion(formal_1_code)
            if idx_conclusion:
                idx_end_conclusion = formal_1_code.rfind(":=")
                conclusion = formal_1_code[idx_conclusion:idx_end_conclusion].strip()
                have_stmt_proof = (
                    f"have {conclusion} := by\n" + indent_code(f"apply_rules [{base_thm_name}]\n" + proof_all_apply, 2) + "\n"
                )
                proof_have = pn_check_proof_sub(
                    server,
                    formal_code,
                    context_env,
                    formal_2_start_line,
                    have_stmt_proof + proof_all_have,
                    timeout_per_proof,
                )
                if proof_have:
                    return True

        # 4. convert using max steps
        for max_step in range(0, 5):
            proof_convert = pn_check_proof_sub(
                server,
                formal_code,
                context_env,
                formal_2_start_line,
                f"convert (config := .unfoldSameFun) {base_thm_name} using {max_step}\n" + proof_all_apply,
                timeout_per_proof,
            )
            if proof_convert:
                return True

        # # 5. aesop fallback
        # proof_aesop = pn_check_proof_sub(
        #     server,
        #     formal_code,
        #     context_env,
        #     formal_2_start_line,
        #     f"aesop",
        #     timeout_per_proof,
        # )
        # if proof_aesop:
        #     return True

        return False

    @staticmethod
    async def _check_equivalence_PQ_async(
        repl: REPL,
        init_env: Environment,
        header: str,
        code_P: str,
        code_Q: str,
        async_generate,
        args: object,
        relations_snippet: str = "",
        exp_type: Optional[str] = None,
        dependency_prompt: str = "",
        attempt_recorder: Optional[object] = None,
        direction: str = "pq",
    ) -> Tuple[bool, list]:
        header = pn_header_or_default(header, relations_snippet)
        code_P = code_P or ""
        code_Q = code_Q or ""
        if "theorem thm_P" not in code_P or "theorem thm_Q" not in code_Q:
            raise ValueError('normalize_thm_names produced invalid Lean theorems')
        code_Q = re.sub(r":=(\s*(by)*\n*)*sorry", ":= by", code_Q).strip()
        assert code_Q.endswith(":= by")
        # Ensure thm_P ends with a stub opener ":= by sorry" to avoid collisions
        code_P = re.sub(r":=(\s*(by)*\n*)*sorry\s*$", ":= by sorry", code_P, flags=re.MULTILINE).strip()
        if not re.search(r":=\s*by\s*sorry\s*$", code_P):
            if re.search(r":=\s*by\s*$", code_P):
                code_P = re.sub(r":=\s*by\s*$", ":= by sorry", code_P)
            else:
                s = code_P.rstrip()
                if s.endswith(":="):
                    code_P = s + " by sorry"
                else:
                    code_P = s + " := by sorry"
        all_eval_results = []
        last_error: str | None = None
        last_goal: str | None = None

        def _extract_goal(env: Environment) -> str | None:
            if not isinstance(env, Environment):
                return None
            if env.sorries:
                goal_text = env.sorries[0].goal.strip()
                if goal_text:
                    return goal_text
            for message in reversed(env.messages):
                data = getattr(message, 'data', '')
                if isinstance(data, str) and '⊢' in data:
                    candidate = data.strip()
                    if candidate:
                        return candidate
            return None

        async def _run_proof(proof_snippet: str):
            snippet_indented = indent_code(proof_snippet, 2)
            validate_lean_src = code_P + "\n\n" + code_Q + "\n" + snippet_indented + "\n"
            run_result = await repl.run_cmd_async(validate_lean_src, init_env)
            errors: List[str] = []
            if hasattr(run_result, 'messages'):
                errors = [m.data for m in run_result.messages if m.severity == "error" and isinstance(m.data, str)]
            goal_text = _extract_goal(run_result) if isinstance(run_result, Environment) else None
            if errors:
                return False, run_result, "\n".join(errors), goal_text, validate_lean_src
            return True, run_result, "", goal_text, validate_lean_src

        

        # LLM exact: include header + explicit fenced theorems blocks
        autoformalization_block = (
            "Lean Header:\n" +
            "```lean\n" + header.strip() + "\n```\n\n" +
            "Theorem thm_P (ground truth):\n" +
            "```lean\n" + code_P.strip() + "\n```\n\n" +
            "Theorem thm_Q (to prove using thm_P):\n" +
            "```lean\n" + code_Q.strip() + "\n```"
        )
        base_prompt = FastEquivChecker.EQUIV_PROVING_PROMPT_TEMPLATE.replace(
            "{autoformalization_result}", autoformalization_block
        )
        if dependency_prompt:
            base_prompt += "\n\nUseful premises:\n" + dependency_prompt
        # If running DSL with learned/oracle relations, also show relations file content explicitly
        try:
            mode_for_prompt = exp_type or getattr(args, 'experiment_mode', None)
            rel_snippet = relations_snippet or ""
            if mode_for_prompt in {"learned", "oracle"} and rel_snippet.strip():
                base_prompt += (
                    f"\n\nRelations ({mode_for_prompt}):\n" +
                    "```lean\n" + rel_snippet.strip() + "\n```"
                )
        except Exception:
            pass

        try_num = int(getattr(args, 'checker_generate_queries', 8) or 8)
        num_samples = max(1, int(getattr(args, 'checker_num_samples', 1) or 1))
        max_tokens = int(getattr(args, 'checker_max_tokens', 1024) or 1024)
        temperature = float(getattr(args, 'checker_temperature', 0.2))
        equiv_api_url = getattr(args, 'checker_equiv_url', '') or ''

        def _build_refine_prompt(base: str, err: Optional[str], goal: Optional[str]) -> str:
            if not err and not goal:
                return base
            parts: list[str] = [base, "", "Previous attempt failed."]
            if err:
                error_excerpt = err.strip()
                if len(error_excerpt) > 1500:
                    error_excerpt = "..." + error_excerpt[-1500:]
                parts += ["Lean messages:", "```", error_excerpt, "```"]
            if goal:
                goal_excerpt = goal.strip()
                if len(goal_excerpt) > 1200:
                    goal_excerpt = "..." + goal_excerpt[-1200:]
                parts += ["Goal at failure:", "```lean", goal_excerpt, "```"]
            parts.append(
                "Revise the proof of `thm_Q` using `thm_P` so that it type-checks in Lean 4. "
                "Address the diagnosed issue explicitly, adjust or replace problematic tactics, and avoid repeating failing steps. "
                "Return exactly one Markdown code block containing only the corrected Lean proof."
            )
            return "\n".join(parts)

        def _validate_equiv_proof_text(text: str) -> None:
            assert not any(t in text for t in FastEquivChecker.BANNED_TOKENS)
            for line in text.split('\n'):
                if line.strip():
                    assert any(tac in line for tac in FastEquivChecker.ALLOWED_TACTICS)

        for attempt in range(int(try_num)):
            prompt = _build_refine_prompt(base_prompt, last_error, last_goal)

            final_output = await async_generate(
                input_prompt=prompt,
                url=equiv_api_url + "/generate",
                sampling_params=dict(
                    n=num_samples,
                    max_tokens=max_tokens,
                    temperature=temperature,
                ),
            )

            outputs = final_output.outputs if getattr(final_output, 'outputs', None) else []
            if not outputs:
                last_error = "LLM generate returned no outputs"
                all_eval_results.append({"exception": last_error})
                continue

            for sample_idx, output in enumerate(outputs):
                try:
                    all_eval_results.append(dict())
                    equiv_proof = extract_first_code_block(output.text, FastEquivChecker.CODEBLOCK_PATTERN).strip()
                    _validate_equiv_proof_text(equiv_proof)
                    all_eval_results[-1]["equiv_proof"] = equiv_proof
                    # record model interaction
                    all_eval_results[-1]["prompt"] = prompt
                    all_eval_results[-1]["response_text"] = output.text
                    ok, run_result, error_text, goal_text, validate_lean_src = await _run_proof(equiv_proof)
                    if callable(attempt_recorder):
                        attempt_recorder(dict(
                            prompt=prompt,
                            response_text=output.text,
                            proof_code=equiv_proof,
                            validate_lean=validate_lean_src,
                            is_success=bool(ok),
                            error_excerpt=error_text,
                            goal_excerpt=goal_text,
                        ))
                    all_eval_results[-1]["validate_lean"] = validate_lean_src
                    if ok:
                        all_eval_results[-1] |= dict(run_result=run_result.serialize())
                        is_success = True
                        return True, all_eval_results
                    last_error = error_text or "Lean typecheck failed"
                    last_goal = goal_text or last_goal
                    all_eval_results[-1]["lean_error"] = last_error
                except Exception as e:
                    all_eval_results[-1] |= dict(exception=str(e))
                    last_error = str(e)

        return False, all_eval_results

   

    

    def _job_worker_task(self, run_meta: dict, full_name: str, pred_idx: int, sample: dict, pred: dict, method: str, direction: str) -> dict:
        """Process a single-direction, single-method task for one prediction.

        Returns a lightweight dict to be merged later:
        {full_name, pred_idx, method, direction, ok, details?}
        """
        a = self.args
        resp: dict = dict(full_name=full_name, pred_idx=int(pred_idx), method=method, direction=direction)

        # If typecheck has failed upstream, short-circuit
        if not (pred.get('typecheck_result', {}).get('is_success', True)):
            resp['ok'] = False
            # Return a record for parent-side aggregation
            resp['record'] = dict(
                problem_id=full_name,
                pred_idx=int(pred_idx),
                strategy=method,
                direction=direction,
                ok=False,
                info={'skipped': 'typecheck_failed'},
                header_src=None,
                thm_P=None,
                thm_Q=None,
                pred_payload=pred,
                # run meta
                run_key=run_meta.get('run_key'),
                run_dir=run_meta.get('run_dir'),
                model=run_meta.get('model'),
                method=run_meta.get('method'),
                experiment_mode=run_meta.get('experiment_mode'),
                dataset=run_meta.get('dataset'),
            )
            return resp 

        # Optional walltime guard for the entire worker task
        class _WorkerTimeout(Exception):
            pass
        walltime = 0
        try:
            walltime = int(getattr(a, 'checker_worker_walltime', 0) or 0)
        except Exception:
            walltime = 0
        _old_alarm_handler = None
        if walltime and walltime > 0:
            try:
                def _timeout_handler(signum, frame):
                    raise _WorkerTimeout()
                _old_alarm_handler = signal.signal(signal.SIGALRM, _timeout_handler)
                signal.alarm(walltime)
            except Exception:
                _old_alarm_handler = None

        # Ignore upstream typecheck_result from predictions; perform our own checking downstream.

        gt_header = sample.get("header")
        gt_header_wo_helper = sample.get("header_wo_helper")
        gt_open = remove_imports(gt_header).strip()
        gt_open_wo_helper = remove_imports(gt_header_wo_helper).strip()
        gt_stmt = sample.get("formal_stmt").strip()

        if not isinstance(gt_stmt, str) or not gt_stmt.strip():
            resp['ok'] = False
            resp['exception'] = 'missing formal_stmt (ground truth)'
            # Return a record for parent-side aggregation
            resp['record'] = dict(
                problem_id=full_name,
                pred_idx=int(pred_idx),
                strategy=method,
                direction=direction,
                ok=False,
                info={'skipped': 'missing_ground_truth'},
                header_src=None,
                thm_P=None,
                thm_Q=None,
                pred_payload=pred,
                # run meta
                run_key=run_meta.get('run_key'),
                run_dir=run_meta.get('run_dir'),
                model=run_meta.get('model'),
                method=run_meta.get('method'),
                experiment_mode=run_meta.get('experiment_mode'),
                dataset=run_meta.get('dataset'),
            )
            return resp

        # Normalize names
        pred_full = pred.get("formal_stmt_pred")
        pred_full = add_newlines_to_full_theorem(pred_full)

        pred_full_wo_imports = remove_imports(pred_full)
        pred_open, pred_stmt = separate_open_theorem(pred_full_wo_imports)
        pred_open = pred_open.strip()
        pred_stmt = pred_stmt.strip()


        problem_name = sample.get("problem_name", full_name)
        gt_stmt_n, pred_stmt_n = pn_normalize_thm_names(gt_stmt, pred_stmt, problem_name)

        # Prepare header with per-task relations (by experiment_mode)
        # base_header = sample.get("header_wo_helper", sample.get("header", ""))
        exp_mode_task = run_meta.get('experiment_mode')
        dataset_task = run_meta.get('dataset')
        relations_snippet = self._resolve_relations_snippet(experiment_mode=exp_mode_task, dataset=dataset_task)

        if exp_mode_task == "oracle":
            header_src = f"{relations_snippet}\n\n\n{gt_open_wo_helper}\n\n\n{pred_open}"
        elif exp_mode_task == "learned":
            header_src = f"{relations_snippet}\n\n\n{gt_open}\n\n\n{pred_open}"
        elif exp_mode_task == "barebone":
            header_src = f"import Mathlib\n\n\n{gt_open_wo_helper}\n\n\n{pred_open}"
        else:
            raise ValueError(f"Unknown experiment mode: {exp_mode_task}")

        try:
            if method == 'beq_plus':
                lean_version = getattr(a, 'checker_leaninteract_lean_version', 'v4.7.0-rc2')
                timeout = getattr(a, 'checker_timeout', FastEquivChecker.DEFAULT_TIMEOUT)
                verbose = bool(getattr(a, 'checker_leaninteract_verbose', False))
                repl_config = LeanREPLConfig(project=TempRequireProject(lean_version=lean_version, require="mathlib"), verbose=verbose)

                if direction == 'pq':
                        ok = FastEquivChecker._beq_single_direction(
                            base_thm=gt_stmt_n,
                            reform_thm=pred_stmt_n,
                            src_header=header_src,
                            repl_config=repl_config,
                            timeout_per_proof=timeout,
                            verbose=verbose,
                        )
                else:
                    ok = FastEquivChecker._beq_single_direction(
                        base_thm=pred_stmt_n,
                        reform_thm=gt_stmt_n,
                        src_header=header_src,
                        repl_config=repl_config,
                        timeout_per_proof=timeout,
                        verbose=verbose,
                    )
                resp['ok'] = bool(ok)
                # Prepare a record for parent-side aggregation
                thmP, thmQ = (gt_stmt_n, pred_stmt_n) if direction == 'pq' else (pred_stmt_n, gt_stmt_n)
                resp['record'] = dict(
                    problem_id=full_name,
                    pred_idx=int(pred_idx),
                    strategy='beq_plus',
                    direction=direction,
                    ok=bool(ok),
                    info=None,
                    header_src=header_src,
                    thm_P=thmP,
                    thm_Q=thmQ,
                    pred_payload=pred,
                    # run meta
                    run_key=run_meta.get('run_key'),
                    run_dir=run_meta.get('run_dir'),
                    model=run_meta.get('model'),
                    method=run_meta.get('method'),
                    experiment_mode=run_meta.get('experiment_mode'),
                    dataset=run_meta.get('dataset'),
                )
                return resp

            elif method == 'llm':
                # Resolve roots
                root_dir = getattr(a, 'root_dir', '.')
                repl_rel = getattr(a, 'checker_repl_root', None)
                mathlib_rel = getattr(a, 'checker_mathlib_root', None)
                repl_root = os.path.join(root_dir, repl_rel) if repl_rel else None
                project_root = os.path.join(root_dir, mathlib_rel) if mathlib_rel else None

                # LLM API config
                equiv_api_url = getattr(a, 'checker_equiv_url', None)
                equiv_model = getattr(a, 'checker_equiv_model', None)
                equiv_token = (
                    os.environ.get('OPENROUTER_API_KEY')
                    or os.environ.get('OPENAI_API_KEY')
                )

                # Build premises prompt if available
                premises_prompt = ""
                premises_dict = getattr(a, 'premises_dict', None)
                if premises_dict:
                    blocks = []
                    for entry in sample.get('hard_dependencies', []):
                        if isinstance(entry, dict):
                            header = (entry.get('header') or "").replace('🔗<|PREMISE|>🔗', '').strip()
                            code = (entry.get('code') or entry.get('formal_stmt') or "").strip()
                            informal = (entry.get('informalization') or "").strip()
                            parts = []
                            if header:
                                parts.append("```lean\n" + header + "\n```")
                            if code:
                                parts.append("```lean\n" + code[:1200] + "\n```")
                            if informal:
                                parts.append("Informal: " + informal[:600])
                            blocks.append("\n".join(parts))
                    for name in sample.get('mathlib_dependencies', []):
                        if isinstance(name, str) and name in premises_dict:
                            entry = premises_dict[name]
                            header = (entry.get('header') or "").replace('🔗<|PREMISE|>🔗', '').strip()
                            informal = (entry.get('informalization') or "").strip()
                            parts = [f"Premise {name}"]
                            if header:
                                parts.append("```lean\n" + header + "\n```")
                            if informal:
                                parts.append("Informal: " + informal[:600])
                            blocks.append("\n".join(parts))
                    premises_prompt = "\n\n".join(blocks)

                # Build async generator and REPL
                async_generate = build_async_text_generator(
                    api_url=equiv_api_url,
                    model=str(equiv_model) if equiv_model else "",
                    token=equiv_token,
                    retries=5,
                )

                repl = REPL(repl_root=repl_root, project_root=project_root)
                repl._run_interactive()
                loop = asyncio.new_event_loop()
                asyncio.set_event_loop(loop)
                try:
                    loop.run_until_complete(asyncio.sleep(INIT_WAIT_TIME))
                    init_env = loop.run_until_complete(repl.run_cmd_async(header_src))

                    # Baseline compile check for generated targets (ensure headers+theorems compile with sorry)
                    def _ensure_sorry(thm_src: str, thm_name: str) -> str:
                        s = thm_src or ""
                        if not s.strip():
                            return s
                        # Normalize to have a stub body
                        s = re.sub(r":=(\s*(by)*\n*)*sorry\s*$", ":= by sorry", s, flags=re.MULTILINE).strip()
                        if not re.search(r":=\s*by\s*sorry\s*$", s):
                            if re.search(r":=\s*by\s*$", s):
                                s = re.sub(r":=\s*by\s*$", ":= by sorry", s)
                            else:
                                s = s.rstrip()
                                if s.endswith(":="):
                                    s = s + " by sorry"
                                else:
                                    s = s + " := by sorry"
                        return s

                    if direction == 'pq':
                        base_src = gt_stmt_n
                        target_src = pred_stmt_n
                    else:
                        base_src = pred_stmt_n.replace("theorem thm_Q", "theorem thm_P")
                        target_src = gt_stmt_n.replace("theorem thm_P", "theorem thm_Q")
                    baseline_src = base_src + "\n\n" + _ensure_sorry(target_src, "thm_Q") + "\n"
                    baseline_run = loop.run_until_complete(repl.run_cmd_async(baseline_src, init_env))
                    compile_ok = True
                    compile_errors: List[str] = []
                    if hasattr(baseline_run, 'messages'):
                        compile_errors = [m.data for m in baseline_run.messages if getattr(m, 'severity', '') == 'error' and isinstance(m.data, str)]
                        compile_ok = len(compile_errors) == 0
                    if not compile_ok:
                        resp['ok'] = False
                        resp['details'] = {'compile_errors': compile_errors[-3:]}
                        resp['record'] = dict(
                            problem_id=full_name,
                            pred_idx=int(pred_idx),
                            strategy='llm',
                            direction=direction,
                            ok=False,
                            info={'compile_errors': compile_errors[-3:]},
                            header_src=header_src,
                            thm_P=(gt_stmt_n if direction=='pq' else pred_stmt_n.replace("theorem thm_Q", "theorem thm_P")),
                            thm_Q=(pred_stmt_n if direction=='pq' else gt_stmt_n.replace("theorem thm_P", "theorem thm_Q")),
                            pred_payload=pred,
                            run_key=run_meta.get('run_key'),
                            run_dir=run_meta.get('run_dir'),
                            model=run_meta.get('model'),
                            method=run_meta.get('method'),
                            experiment_mode=run_meta.get('experiment_mode'),
                            dataset=run_meta.get('dataset'),
                            compile_ok=False,
                        )
                        return resp

                    if direction == 'pq':
                        ok, details = loop.run_until_complete(
                            FastEquivChecker._check_equivalence_PQ_async(
                                repl, init_env, header_src,
                                gt_stmt_n, pred_stmt_n,
                                async_generate, a,
                                relations_snippet, exp_mode_task,
                                premises_prompt,
                                attempt_recorder=None, direction='pq'
                            )
                        )
                    else:
                        ok, details = loop.run_until_complete(
                            FastEquivChecker._check_equivalence_PQ_async(
                                repl, init_env, header_src,
                                pred_stmt_n.replace("theorem thm_Q", "theorem thm_P"),
                                gt_stmt_n.replace("theorem thm_P", "theorem thm_Q"),
                                async_generate, a,
                                relations_snippet, exp_mode_task,
                                premises_prompt,
                                attempt_recorder=None, direction='qp'
                            )
                        )
                    resp['ok'] = bool(ok)
                    resp['details'] = details
                    # Prepare a record for parent-side aggregation
                    resp['record'] = dict(
                        problem_id=full_name,
                        pred_idx=int(pred_idx),
                        strategy='llm',
                        direction=direction,
                        ok=bool(ok),
                        info=details,
                        header_src=header_src,
                        thm_P=(gt_stmt_n if direction=='pq' else pred_stmt_n.replace("theorem thm_Q", "theorem thm_P")),
                        thm_Q=(pred_stmt_n if direction=='pq' else gt_stmt_n.replace("theorem thm_P", "theorem thm_Q")),
                        pred_payload=pred,
                        # run meta
                        run_key=run_meta.get('run_key'),
                        run_dir=run_meta.get('run_dir'),
                        model=run_meta.get('model'),
                        method=run_meta.get('method'),
                        experiment_mode=run_meta.get('experiment_mode'),
                        dataset=run_meta.get('dataset'),
                        compile_ok=True,
                    )
                    return resp
                finally:
                    from contextlib import suppress
                    with suppress(Exception):
                        repl._close()
                    with suppress(Exception):
                        loop.close()
            else:
                resp['ok'] = False
                resp['exception'] = f'unknown method: {method}'
                return resp
        except _WorkerTimeout:
            resp['ok'] = False
            resp['exception'] = 'worker_timeout'
            # Return a record for parent-side aggregation on timeout
            resp['record'] = dict(
                problem_id=full_name,
                pred_idx=int(pred_idx),
                strategy=method,
                direction=direction,
                ok=False,
                info={'timeout': True},
                header_src=None,
                thm_P=None,
                thm_Q=None,
                pred_payload=pred,
                # run meta
                run_key=run_meta.get('run_key'),
                run_dir=run_meta.get('run_dir'),
                model=run_meta.get('model'),
                method=run_meta.get('method'),
                experiment_mode=run_meta.get('experiment_mode'),
                dataset=run_meta.get('dataset'),
            )
            return resp
        except Exception as e:
            resp['ok'] = False
            resp['exception'] = str(e)
            # Return a record for parent-side aggregation on failure
            resp['record'] = dict(
                problem_id=full_name,
                pred_idx=int(pred_idx),
                strategy=method,
                direction=direction,
                ok=False,
                info={'exception': str(e)},
                header_src=None,
                thm_P=None,
                thm_Q=None,
                pred_payload=pred,
                # run meta
                run_key=run_meta.get('run_key'),
                run_dir=run_meta.get('run_dir'),
                model=run_meta.get('model'),
                method=run_meta.get('method'),
                experiment_mode=run_meta.get('experiment_mode'),
                dataset=run_meta.get('dataset'),
            )
            return resp
        finally:
            # Clear any pending alarm and restore handler
            with contextlib.suppress(Exception):
                signal.alarm(0)
            if _old_alarm_handler is not None:
                with contextlib.suppress(Exception):
                    signal.signal(signal.SIGALRM, _old_alarm_handler)
    



# Backward-compatible alias used internally by this module
EquivChecker = FastEquivChecker
CheckerFast = FastEquivChecker

if __name__ == "__main__":
    import argparse
    import sys

    parser = argparse.ArgumentParser(description="ProofNet Equivalence Checker CLI")
    subparsers = parser.add_subparsers(dest='command', help='Available commands')

    # Run command: perform equivalence checking across discovered outputs
    run_parser = subparsers.add_parser('run', help='Run fast equivalence checking across outputs/*')
    run_parser.add_argument('--input', required=False, help='(Deprecated) Single results JSON; omit to scan outputs/')
    run_parser.add_argument('--root_dir', default='.', help='Project root directory')
    run_parser.add_argument('--base_output_dir', dest='base_output_dir', default=None, help='Directory or file to write checker outputs')
    # Dataset and experiment type, used to resolve DSL relations header
    run_parser.add_argument('--dataset', default=None, help='Dataset name (e.g., DSL)')
    run_parser.add_argument('--strategies', nargs='+', default=['beq_plus'], help='Strategies to run: beq_plus, llm')
    run_parser.add_argument('--eval_set', default='proofnet', help='Eval set name for checker')
    run_parser.add_argument('--num_concurrency', type=int, default=16, help='Parallel workers for checking')
    run_parser.add_argument('--timeout', type=int, default=60, help='Timeout (seconds) per direction')
    run_parser.add_argument('--lean_version', default='v4.7.0-rc2', help='LeanInteract Lean version tag')
    run_parser.add_argument('--verbose', action='store_true', help='Verbose LeanInteract output')
    run_parser.add_argument('--quiet', action='store_true', help='Silence per-sample logs')
    run_parser.add_argument('--progress', action='store_true', default=True, help='Show progress bar')
    run_parser.add_argument('--mathlib_root', default=None, help='Path to mathlib root')
    run_parser.add_argument('--repl_root', default=None, help='Path to Lean REPL project root')
    # Optional: DSL ground-truth CSV for headers/formal
    run_parser.add_argument('--gt_csv', default=None, help='Path to DSL CSV ground-truth file (headers/formal)')
    # LLM strategy params
    run_parser.add_argument('--equiv_url', default=None, help='Equivalence API base URL')
    run_parser.add_argument('--equiv_model', default=None, help='Equivalence model id')
    run_parser.add_argument('--generate_queries', type=int, default=8, help='LLM self-refine attempts')
    run_parser.add_argument('--num_samples', type=int, default=1, help='Number of samples per LLM call')
    run_parser.add_argument('--max_tokens', type=int, default=2048, help='Max tokens per LLM call')
    run_parser.add_argument('--temperature', type=float, default=0.2, help='Sampling temperature')
    run_parser.add_argument('--stat_mode', choices=['per_problem', 'per_prediction'], default='per_prediction', help='Statistics aggregation mode')
    run_parser.add_argument('--detailed_logs_dir', default=None, help='Optional directory for detailed logs')
    # Fast scanner roots
    run_parser.add_argument('--scan_roots', nargs='*', default=None, help='Roots to scan for *_result.json (default: <root_dir>/outputs)')
    # Optional: walltime per worker task
    run_parser.add_argument('--worker_walltime', type=int, default=None, help='Walltime seconds per worker task')
    # Debug: limit total tasks (problem×pred×strategy×direction)
    run_parser.add_argument('--limit_tasks', type=int, default=None, help='Debug: limit total tasks created to N')

    args = parser.parse_args()

    if args.command == 'run':
        try:
            # Prepare args namespace for checker class (support both plain and checker_* keys)
            # Preserve dataset/experiment_type as-is for FastEquivChecker to consume
            setattr(args, 'checker_eval_set', getattr(args, 'eval_set', 'proofnet'))
            setattr(args, 'checker_num_concurrency', getattr(args, 'num_concurrency', 16))
            setattr(args, 'checker_timeout', getattr(args, 'timeout', 60))
            setattr(args, 'checker_leaninteract_lean_version', getattr(args, 'lean_version', None))
            setattr(args, 'checker_leaninteract_verbose', getattr(args, 'verbose', False))
            setattr(args, 'checker_quiet', getattr(args, 'quiet', False))
            setattr(args, 'checker_progress', getattr(args, 'progress', True))
            setattr(args, 'checker_mathlib_root', getattr(args, 'mathlib_root', None))
            setattr(args, 'checker_repl_root', getattr(args, 'repl_root', None))
            setattr(args, 'checker_equiv_url', getattr(args, 'equiv_url', None))
            setattr(args, 'checker_equiv_model', getattr(args, 'equiv_model', None))
            setattr(args, 'checker_generate_queries', getattr(args, 'generate_queries', None))
            setattr(args, 'checker_num_samples', getattr(args, 'num_samples', None))
            setattr(args, 'checker_max_tokens', getattr(args, 'max_tokens', None))
            setattr(args, 'checker_temperature', getattr(args, 'temperature', None))
            setattr(args, 'checker_stat_mode', getattr(args, 'stat_mode', 'per_prediction'))
            setattr(args, 'checker_base_output_dir', getattr(args, 'base_output_dir', None))
            setattr(args, 'checker_strategies', getattr(args, 'strategies', None))
            setattr(args, 'checker_limit_tasks', getattr(args, 'limit_tasks', None))
            # worker walltime
            setattr(args, 'checker_worker_walltime', getattr(args, 'worker_walltime', None))
            # expose gt_csv directly
            setattr(args, 'checker_gt_csv', getattr(args, 'gt_csv', None))

            # Configure fastchecker scan roots
            if getattr(args, 'scan_roots', None):
                setattr(args, 'fastchecker_scan_roots', [os.path.join(args.root_dir, r) if not os.path.isabs(r) else r for r in args.scan_roots])

            # Run fast aggregation across outputs; --input is ignored in fast mode
            checker = FastEquivChecker(args=args)
            checked = checker.run(output_path=args.base_output_dir)
            # Compute a robust count across both method views for user-facing message
            try:
                built_views = checker.results_manager.build_results_from_logs(strategies=getattr(args, 'checker_strategies', []) or [], run_idx=0)
                beq_keys = set((built_views.get('beq_view') or {}).keys())
                gen_keys = set((built_views.get('gen_view') or {}).keys())
                total_problems = len(beq_keys | gen_keys)
            except Exception:
                total_problems = len(checked) if isinstance(checked, dict) else 0
            # Write merged summaries if applicable is already handled in manager when caller requests
            print(f"Checked {total_problems} problems. Results saved under: {checker.results_manager.base_output_dir}")
        except Exception as e:
            print(f"Error during run: {e}", file=sys.stderr)
            sys.exit(1)

    else:
        parser.print_help()
