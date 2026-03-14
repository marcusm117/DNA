from __future__ import annotations

import json
import os
import os.path as osp
from typing import Any, Dict, List, Optional


class EquivalenceResultsAnalyzer:
    """Utilities to merge checker results and compute accuracy summaries.

    Decouples analysis from checker runtime so pipelines and tools can reuse it.
    """

    @staticmethod
    def _extract_pq_qp(pred: Dict[str, Any]) -> tuple[bool, bool]:
        """Best-effort extraction of per-direction success flags from a prediction entry.

        Supports both legacy keys (equivcheck_results_PQ/QP) and the newer
        strategy_results.{beq_plus|llm}.{pq_ok, qp_ok} layout.
        """
        if not isinstance(pred, dict):
            return False, False
        # Legacy per-direction fields
        pq_ok = bool(pred.get('equivcheck_results_PQ', {}).get('is_success', False))
        qp_ok = bool(pred.get('equivcheck_results_QP', {}).get('is_success', False))
        if pq_ok or qp_ok:
            return pq_ok, qp_ok
        # Newer strategy_results layout
        sr = pred.get('strategy_results')
        if isinstance(sr, dict):
            # Prefer beq_plus if available, otherwise llm; otherwise OR across any
            for key in ('beq_plus', 'llm'):
                if key in sr and isinstance(sr[key], dict):
                    pq_ok = bool(sr[key].get('pq_ok', False))
                    qp_ok = bool(sr[key].get('qp_ok', False))
                    return pq_ok, qp_ok
            # Fallback: any strategy
            any_pq = any(bool(v.get('pq_ok', False)) for v in sr.values() if isinstance(v, dict))
            any_qp = any(bool(v.get('qp_ok', False)) for v in sr.values() if isinstance(v, dict))
            return any_pq, any_qp
        return False, False

    @staticmethod
    def merge_results_dicts(results_list: List[Dict[str, list]]) -> Dict[str, list]:
        from copy import deepcopy as _dc
        all_keys = set()
        for r in results_list:
            all_keys.update(r.keys())
        merged: Dict[str, list] = {}
        for key in all_keys:
            present = [r[key] for r in results_list if key in r]
            if not present:
                continue
            base = _dc(present[0])
            n = min(len(lst) for lst in present)
            for i in range(n):
                pq_any = False
                qp_any = False
                for lst in present:
                    if isinstance(lst[i], dict):
                        pq_i, qp_i = EquivalenceResultsAnalyzer._extract_pq_qp(lst[i])
                        pq_any = pq_any or pq_i
                        qp_any = qp_any or qp_i
                # Normalize into legacy-equivalent fields for downstream consumers
                base_pq = base[i].get('equivcheck_results_PQ', {}) if isinstance(base[i], dict) else {}
                base_qp = base[i].get('equivcheck_results_QP', {}) if isinstance(base[i], dict) else {}
                if isinstance(base[i], dict):
                    base[i]['equivcheck_results_PQ'] = {'is_success': bool(pq_any), 'result': base_pq.get('result')}
                    base[i]['equivcheck_results_QP'] = {'is_success': bool(qp_any), 'result': base_qp.get('result')}
                    base[i].setdefault('equivcheck_results', {})
                    base[i]['equivcheck_results']['merged'] = {'is_success': bool(pq_any and qp_any)}
            merged[key] = base[:n]
        return merged

    @classmethod
    def build_equiv_summary(
        cls,
        *,
        results: Optional[Dict[str, list]] = None,
        results_file: Optional[str] = None,
        results_files: Optional[List[str]] = None,
        output_file: Optional[str] = None,
        stat_mode: str = "per_problem",
    ) -> Dict[str, Any]:
        if results is None:
            if results_files:
                loaded: List[Dict[str, list]] = []
                for rf in results_files:
                    try:
                        with open(rf, 'r', encoding='utf-8') as f:
                            loaded.append(json.load(f))
                    except Exception:
                        pass
                if not loaded:
                    raise FileNotFoundError("No valid results files provided")
                results = cls.merge_results_dicts(loaded)
            elif results_file is not None:
                try:
                    with open(results_file, 'r', encoding='utf-8') as f:
                        results = json.load(f)
                except Exception as e:
                    raise FileNotFoundError(f"Failed to load results from {results_file}: {e}")
            else:
                raise ValueError("Either 'results', 'results_file', or 'results_files' must be provided")

        if not isinstance(results, dict):
            raise ValueError("Results must be a dictionary")

        # Container for detailed entries; name kept for per-problem branch.
        per_problem: Dict[str, Dict[str, bool]] = {}

        if stat_mode == "per_prediction":
            total = 0
            c_type = c_pq = c_qp = c_beq = c_likely = 0
            per_pred: Dict[str, Dict[str, Any]] = {}
            for full_name, preds in results.items():
                if isinstance(preds, dict):
                    preds = [preds]
                if not preds:
                    continue
                for idx, pred in enumerate(preds):
                    if not isinstance(pred, dict):
                        continue
                    total += 1
                    type_ok = bool(pred.get('typecheck_result', {}).get('is_success', False))
                    pq_ok, qp_ok = cls._extract_pq_qp(pred)
                    beq_ok = bool(pq_ok and qp_ok)
                    likely_ok = bool(pq_ok or qp_ok)
                    c_type += int(type_ok)
                    c_pq += int(pq_ok)
                    c_qp += int(qp_ok)
                    c_beq += int(beq_ok)
                    c_likely += int(likely_ok)

                    pred_idx = pred.get('pred_idx', idx)
                    key = f"{full_name}::pred_{pred_idx}"
                    per_pred[key] = {
                        'problem_name': full_name,
                        'pred_idx': int(pred_idx),
                        'type': type_ok,
                        'pq': bool(pq_ok),
                        'qp': bool(qp_ok),
                        'beq': bool(beq_ok),
                        'likelybeq': bool(likely_ok),
                    }

            summary = {
                'stat_mode': 'per_prediction',
                'total': total,
                'total_description': 'Total predictions',
                'acc_type': c_type / max(1, total),
                'acc_pq': c_pq / max(1, total),
                'acc_qp': c_qp / max(1, total),
                'acc_beq': c_beq / max(1, total),
                'acc_likelybeq': c_likely / max(1, total),
                'predictions': per_pred,
            }
            if output_file:
                with open(output_file, 'w', encoding='utf-8') as f:
                    json.dump({'summary': summary}, f, indent=2)
            return {'summary': summary}

        else:  # per_problem
            total = 0
            c_type = c_pq = c_qp = c_beq = c_likely = 0
            for full_name, preds in results.items():
                if isinstance(preds, dict):
                    preds = [preds]
                if not preds:
                    continue
                type_ok_any = any((isinstance(p, dict) and p.get('typecheck_result', {}).get('is_success', False)) for p in preds)
                pq_ok_any = any((isinstance(p, dict) and cls._extract_pq_qp(p)[0]) for p in preds)
                qp_ok_any = any((isinstance(p, dict) and cls._extract_pq_qp(p)[1]) for p in preds)
                beq_any = any((isinstance(p, dict) and (cls._extract_pq_qp(p)[0] and cls._extract_pq_qp(p)[1])) for p in preds)
                likely_any = any((isinstance(p, dict) and (cls._extract_pq_qp(p)[0] or cls._extract_pq_qp(p)[1])) for p in preds)
                total += 1
                c_type += int(type_ok_any)
                c_pq += int(pq_ok_any)
                c_qp += int(qp_ok_any)
                c_beq += int(beq_any)
                c_likely += int(likely_any)
                per_problem[full_name] = {
                    'type': type_ok_any,
                    'pq': pq_ok_any,
                    'qp': qp_ok_any,
                    'beq': beq_any,
                    'likelybeq': likely_any,
                }

            summary = {
                'stat_mode': 'per_problem',
                'total': total,
                'total_description': 'Total problems',
                'acc_type': c_type / max(1, total),
                'acc_pq': c_pq / max(1, total),
                'acc_qp': c_qp / max(1, total),
                'acc_beq': c_beq / max(1, total),
                'acc_likelybeq': c_likely / max(1, total),
                'problems': per_problem,
            }
            if output_file:
                with open(output_file, 'w', encoding='utf-8') as f:
                    json.dump({'summary': summary}, f, indent=2)
            return {'summary': summary}


    @classmethod
    def build_equiv_summary_by_run(
        cls,
        *,
        results: Dict[str, list],
        stat_mode: str = "per_problem",
    ) -> Dict[str, Any]:
        """Compute summaries for each prediction index across problems.

        For run i, only the i-th prediction of each problem (if present) contributes.
        Returns a mapping from run index (as string) to a standard summary dict.
        """
        if not isinstance(results, dict):
            raise ValueError("Results must be a dictionary")

        # Determine maximum number of predictions over all problems
        max_len = 0
        for preds in results.values():
            if isinstance(preds, dict):
                max_len = max(max_len, 1)
            elif isinstance(preds, list):
                max_len = max(max_len, len(preds))

        by_run: Dict[str, Any] = {}
        for i in range(max_len):
            # Collect i-th predictions for problems that have it
            temp: Dict[str, list] = {}
            for name, preds in results.items():
                if isinstance(preds, list) and i < len(preds) and isinstance(preds[i], dict) and preds[i]:
                    temp[name] = [preds[i]]
                elif isinstance(preds, dict) and i == 0:
                    temp[name] = [preds]
            # Build standard summary for this run
            by_run[str(i)] = cls.build_equiv_summary(results=temp, stat_mode=stat_mode).get('summary', {})

        return {"by_run": by_run}

class EquivalenceResultsManager:
    def __init__(self, *, base_output_dir: Optional[str] = None, detailed_logs_dir: Optional[str] = None) -> None:
        self.base_output_dir = base_output_dir or "."
        self.detailed_logs_dir = detailed_logs_dir  # deprecated: logs kept in-memory
        # In-memory run state (single-run mode)
        self._meta: Dict[str, Any] = {}
        self._events: List[Dict[str, Any]] = []
        # Per-method aggregated views in autoformalization_result-like format
        # { problem_name: [pred_dict, ...] }
        self._mem_views: Dict[str, Dict[str, list]] = {  # keys: 'beq', 'generate'
            'beq': {},
            'generate': {},
        }

    # ---------- paths ----------
    def _run_root(self, run_idx: int) -> str:
        # Deprecated: filesystem logging removed
        return osp.join(self.base_output_dir or ".", "detailed_logs")

    def _problem_root(self, run_idx: int, problem_id: str) -> str:
        # Deprecated: no-op path (kept for compatibility if referenced)
        return osp.join(self._run_root(run_idx), "problems", problem_id)

    def _pred_dir(self, run_idx: int, problem_id: str, strategy: str, pred_idx: int) -> str:
        # Deprecated: no-op path
        return osp.join(self._problem_root(run_idx, problem_id), strategy, f"pred_{pred_idx}")

    # ---------- run lifecycle ----------
    def start_run(self, *, cfg: Dict[str, Any], run_idx: int = 0) -> str:
        # Store config in memory
        self._meta = dict(cfg)
        self._events.clear()
        # Return base output dir for compatibility
        return self.base_output_dir or "."

    def log_event(self, *, payload: Dict[str, Any], run_idx: int = 0) -> None:
        # Append to in-memory events list
        try:
            self._events.append(dict(payload))
        except Exception:
            pass

    # ---------- BEQ logging ----------
    def record_single_direction_result(
        self,
        *,
        problem_id: str,
        pred_idx: int,
        strategy: str,   # 'beq_plus' or 'llm'
        direction: str,  # 'pq' or 'qp'
        ok: bool,
        info: Optional[Dict[str, Any]] = None,
        header_src: Optional[str] = None,
        thm_P: Optional[str] = None,
        thm_Q: Optional[str] = None,
        pred_payload: Optional[Dict[str, Any]] = None,
        run_idx: int = 0,
    ) -> None:
        """Record one single-direction result into an in-memory aggregated view."""
        direction = str(direction or '').lower()
        if direction not in {'pq', 'qp'}:
            direction = 'pq'
        strat = str(strategy or '').lower()
        method_key = 'generate' if strat == 'llm' else 'beq'
        view = self._mem_views.setdefault(method_key, {})

        # Prepare problem entry list sized to pred_idx
        plist = view.setdefault(problem_id, [])
        while len(plist) <= int(pred_idx):
            plist.append({})
        entry = plist[int(pred_idx)] or {}

        # Seed from pred_payload
        if isinstance(pred_payload, dict):
            for k, v in pred_payload.items():
                if k not in entry:
                    entry[k] = v
        entry.setdefault('problem_name', problem_id)
        entry['pred_idx'] = int(pred_idx)
        entry.setdefault('equivcheck_results', {})
        entry.setdefault('strategy_results', {})

        # Strategy-specific sub-entry
        sr = entry['strategy_results'].setdefault(strat, {})
        if direction == 'pq':
            sr['pq_ok'] = bool(ok)
            if info is not None:
                sr['result_PQ'] = info
        else:
            sr['qp_ok'] = bool(ok)
            if info is not None:
                sr['result_QP'] = info

        tag = 'llm' if strat == 'llm' else 'beq_plus'
        pq_ok = bool(sr.get('pq_ok', False))
        qp_ok = bool(sr.get('qp_ok', False))
        entry['equivcheck_results'][tag] = {'is_success': bool(pq_ok and qp_ok)}
        plist[int(pred_idx)] = entry
    def record_beq_prediction(
        self,
        *,
        problem_id: str,
        pred_idx: int,
        header_src: str,
        thm_P: str,
        thm_Q: str,
        pq_ok: bool,
        qp_ok: bool,
        pq_artifacts: Optional[Dict[str, Any]] = None,
        qp_artifacts: Optional[Dict[str, Any]] = None,
        run_idx: int = 0,
    ) -> str:
        # Mirror PQ/QP booleans into in-memory BEQ view
        view = self._mem_views.setdefault('beq', {})
        plist = view.setdefault(problem_id, [])
        while len(plist) <= int(pred_idx):
            plist.append({})
        entry = plist[int(pred_idx)] or {}
        entry.setdefault('problem_name', problem_id)
        entry['pred_idx'] = int(pred_idx)
        entry.setdefault('equivcheck_results', {})
        entry.setdefault('strategy_results', {})
        sr = entry['strategy_results'].setdefault('beq_plus', {})
        sr['pq_ok'] = bool(pq_ok)
        sr['qp_ok'] = bool(qp_ok)
        entry['equivcheck_results']['beq_plus'] = {'is_success': bool(pq_ok and qp_ok)}
        plist[int(pred_idx)] = entry
        return ""

    # ---------- Build results from logs ----------
    def _iter_problem_ids(self, run_idx: int = 0) -> List[str]:
        # Return union of problem ids present in in-memory views
        keys = set()
        for view in self._mem_views.values():
            keys.update(view.keys())
        return sorted(keys)

    def _read_json_safe(self, path: str) -> Optional[Dict[str, Any]]:
        try:
            with open(path, 'r', encoding='utf-8') as f:
                return json.load(f)
        except Exception:
            return None

    def build_results_from_logs(self, *, strategies: List[str], run_idx: int = 0) -> Dict[str, Dict[str, list]]:
        """Return in-memory per-method views.

        Output: { 'beq_view': {...}, 'gen_view': {...} }
        """
        beq_view = json.loads(json.dumps(self._mem_views.get('beq', {})))
        gen_view = json.loads(json.dumps(self._mem_views.get('generate', {})))
        return {'beq_view': beq_view, 'gen_view': gen_view}



    def finalize_run(
        self,
        *,
        strategies: List[str],
        output_path: Optional[str],
        stat_mode: str = "per_prediction",
        run_idx: int = 0,
    ) -> Dict[str, list]:
        print(f"[analysis] Finalizing run: stat_mode={stat_mode}, output_path={output_path or self.base_output_dir}")
        built = self.build_results_from_logs(strategies=strategies, run_idx=run_idx)
        beq_view = built.get('beq_view', {})
        gen_view = built.get('gen_view', {})
        print(f"[analysis] Aggregated views -> beq: {len(beq_view)} problems, generate: {len(gen_view)} problems")

        # Save method results
        save_paths: Dict[str, str] = {}
        # 2025-09: Always write per-method result files, even if empty, to make runs observable.
        save_paths['beq'] = self.save_method_results(method='beq_plus', checked=beq_view, output_path=output_path, tag='beq')
        print(f"[analysis] Saved beq results -> {save_paths['beq']}")
        save_paths['generate'] = self.save_method_results(method='llm', checked=gen_view, output_path=output_path, tag='generate')
        print(f"[analysis] Saved generate results -> {save_paths['generate']}")

        # Write per-method summaries
        # Always write summaries too; they will reflect zeros if views are empty.
        p = self.write_per_method_summary(method='beq_plus', results=beq_view, tag='beq', stat_mode=stat_mode)
        if p:
            print(f"[analysis] Per-method summary (beq): {p}")
        p = self.write_per_method_summary(method='llm', results=gen_view, tag='generate', stat_mode=stat_mode)
        if p:
            print(f"[analysis] Per-method summary (generate): {p}")

        # Write merged summaries if any
        aggregate: Dict[str, Dict[str, list]] = {}
        if beq_view:
            aggregate['beq'] = beq_view
        if gen_view:
            aggregate['generate'] = gen_view
        # Try writing merged summaries regardless; if both empty, analyzer will still produce a valid zero summary.
        merged_paths = self.write_merged_summaries_from_aggregate(
            aggregate=aggregate,
            save_paths=save_paths or None,
            default_out_dir=self.base_output_dir,
            stat_mode=stat_mode,
        )
        if isinstance(merged_paths, dict):
            print(f"[analysis] Merged summaries -> merged: {merged_paths.get('merged')}, by_run: {merged_paths.get('by_run')}")
        print("[analysis] Finalize done.")

        return beq_view or gen_view

    # ---------- Generate logging ----------
    def start_generate_prediction(self, *, run_idx: int, problem_id: str, pred_idx: int, header_src: str, thm_P: str, thm_Q: str) -> str:
        pred_dir = self._pred_dir(run_idx, problem_id, "generate", pred_idx)
        try:
            with open(osp.join(pred_dir, 'meta.json'), 'w', encoding='utf-8') as f:
                json.dump({"header_present": bool(header_src)}, f, indent=2)
        except Exception:
            pass
        return pred_dir

    def record_generate_attempt(
        self,
        *,
        run_idx: int,
        problem_id: str,
        pred_idx: int,
        direction: str,  # 'pq' | 'qp'
        attempt_idx: int,
        prompt: str,
        response_text: str,
        proof_code: str,
        validate_lean: str,
        is_success: bool,
        error_excerpt: Optional[str] = None,
        goal_excerpt: Optional[str] = None,
    ) -> None:
        base = self._pred_dir(run_idx, problem_id, "generate", pred_idx)
        att_dir = osp.join(base, f"attempts_{direction}", f"attempt_{attempt_idx}")
        try:
            os.makedirs(att_dir, exist_ok=True)
            with open(osp.join(att_dir, 'prompt.txt'), 'w', encoding='utf-8') as f:
                f.write(prompt or "")
            with open(osp.join(att_dir, 'response.txt'), 'w', encoding='utf-8') as f:
                f.write(response_text or "")
            with open(osp.join(att_dir, 'proof_extracted.lean'), 'w', encoding='utf-8') as f:
                f.write(proof_code or "")
            vdir = osp.join(att_dir, 'validate')
            os.makedirs(vdir, exist_ok=True)
            with open(osp.join(vdir, 'proof.lean'), 'w', encoding='utf-8') as f:
                f.write(validate_lean or "")
            with open(osp.join(vdir, 'result.json'), 'w', encoding='utf-8') as f:
                json.dump({"is_success": bool(is_success), "lean_error": error_excerpt or "", "goal": goal_excerpt or ""}, f, indent=2)
        except Exception:
            pass

    def finalize_generate_prediction(self, *, run_idx: int, problem_id: str, pred_idx: int, summary: Dict[str, Any]) -> None:
        base = self._pred_dir(run_idx, problem_id, "generate", pred_idx)
        try:
            with open(osp.join(base, 'summary.json'), 'w', encoding='utf-8') as f:
                json.dump(summary, f, indent=2)
        except Exception:
            pass

    @staticmethod
    def _save_path_for(method: str, base_output: Optional[str], out_root: str, tag: str = "") -> str:
        # Use concise, stable filenames per method
        if (tag == 'generate') or (method == 'llm'):
            filename = 'generate.json'
        elif (tag == 'beq') or (method == 'beq_plus'):
            filename = 'beq.json'
        else:
            suffix = f"_{tag}" if tag else ""
            filename = f"autoformalization_equiv_checked{suffix}.json"

        if base_output:
            if base_output.endswith('.json'):
                # place sibling file in same directory; ensure directory exists
                out_dir = osp.dirname(base_output) or "."
                try:
                    os.makedirs(out_dir, exist_ok=True)
                except Exception:
                    # Best-effort; downstream write will raise if this fails
                    pass
                return osp.join(out_dir, filename)
            if os.path.isdir(base_output):
                return osp.join(base_output, filename)
            os.makedirs(base_output, exist_ok=True)
            return osp.join(base_output, filename)

        out_dir = out_root or "."
        os.makedirs(out_dir, exist_ok=True)
        return osp.join(out_dir, filename)

    def save_method_results(self, *, method: str, checked: Dict[str, list], output_path: Optional[str], tag: str = "") -> str:
        save_path = self._save_path_for(method, output_path, self.base_output_dir, tag)
        # Ensure parent directory exists (belt-and-suspenders in case caller passed a file path)
        try:
            out_dir = osp.dirname(save_path) or "."
            os.makedirs(out_dir, exist_ok=True)
        except Exception as e:
            print(f"[analysis] Failed to ensure output dir for {save_path}: {e}")
        # Try writing and surface failure reason instead of swallowing silently
        try:
            with open(save_path, 'w', encoding='utf-8') as f:
                json.dump(checked, f, indent=2, ensure_ascii=False)
            try:
                print(f"[analysis] Wrote {method} results: {save_path} (problems={len(checked) if isinstance(checked, dict) else 'n/a'})")
            except Exception:
                pass
        except Exception as e:
            print(f"[analysis] Failed to write {save_path}: {e}")
        return save_path

    def write_per_method_summary(self, *, method: str, results: Dict[str, list], tag: str = "", stat_mode: str = "per_problem") -> Optional[str]:
        try:
            out_dir = self.base_output_dir or "."
            os.makedirs(out_dir, exist_ok=True)
            summary = EquivalenceResultsAnalyzer.build_equiv_summary(results=results, stat_mode=stat_mode)
            summary_path = osp.join(out_dir, f'equiv_summary_{tag or method}.json')
            with open(summary_path, 'w', encoding='utf-8') as f:
                json.dump(summary, f, indent=2)
            return summary_path
        except Exception:
            return None

    def write_merged_summaries(self, *, merged: Dict[str, list], stat_mode: str = "per_problem") -> Dict[str, Optional[str]]:
        paths = {"merged": None, "by_run": None}
        try:
            out_dir = self.base_output_dir or "."
            os.makedirs(out_dir, exist_ok=True)
            merged_summary = EquivalenceResultsAnalyzer.build_equiv_summary(results=merged, stat_mode=stat_mode)
            merged_summary_path = osp.join(out_dir, 'equiv_summary_merged.json')
            with open(merged_summary_path, 'w', encoding='utf-8') as f:
                json.dump(merged_summary, f, indent=2)
            paths["merged"] = merged_summary_path
            by_run_summary = EquivalenceResultsAnalyzer.build_equiv_summary_by_run(results=merged, stat_mode=stat_mode)
            by_run_path = osp.join(out_dir, 'equiv_summary_by_run.json')
            with open(by_run_path, 'w', encoding='utf-8') as f:
                json.dump(by_run_summary, f, indent=2)
            paths["by_run"] = by_run_path
        except Exception:
            pass
        return paths

    def write_merged_summaries_from_aggregate(
        self,
        *,
        aggregate: Dict[str, Dict[str, list]],
        save_paths: Optional[Dict[str, str]] = None,
        default_out_dir: Optional[str] = None,
        stat_mode: str = "per_problem",
    ) -> Optional[Dict[str, Optional[str]]]:
        try:
            merged_inputs: List[Dict[str, list]] = []
            if 'beq' in aggregate:
                merged_inputs.append(aggregate['beq'])
            if 'generate' in aggregate:
                merged_inputs.append(aggregate['generate'])
            if not merged_inputs:
                return None

            merged = EquivalenceResultsAnalyzer.merge_results_dicts(merged_inputs)

            out_dir = None
            if save_paths:
                try:
                    first_path = next(iter(save_paths.values()))
                    out_dir = osp.dirname(first_path)
                except Exception:
                    out_dir = None
            if not out_dir:
                out_dir = default_out_dir or self.base_output_dir or "."
            self.base_output_dir = out_dir
            return self.write_merged_summaries(merged=merged, stat_mode=stat_mode)
        except Exception:
            return None

    def record_equiv_attempt(
        self,
        *,
        run_idx: int,
        problem_id: str,
        prediction_idx: int,
        strategy: str,
        header_src: str,
        gt_stmt_n: str,
        pred_stmt_n: str,
        is_success_PQ: Any,
        is_success_QP: Any,
        result_PQ: Any,
        result_QP: Any,
    ) -> None:
        if not self.detailed_logs_dir:
            return
        try:
            base = osp.join(self.detailed_logs_dir, f"run_{run_idx}", problem_id, "equivalence_checking", "strategies", strategy)
            os.makedirs(base, exist_ok=True)
            payload = {
                "prediction_idx": prediction_idx,
                "strategy": strategy,
                "header": header_src,
                "thm_P": gt_stmt_n,
                "thm_Q": pred_stmt_n,
                "PQ_success": bool(is_success_PQ),
                "QP_success": bool(is_success_QP),
                "PQ_results": result_PQ,
                "QP_results": result_QP,
            }
            path = osp.join(base, f"pred_{prediction_idx}.json")
            with open(path, 'w', encoding='utf-8') as f:
                json.dump(payload, f, ensure_ascii=False, indent=2)
        except Exception:
            pass

    @classmethod
    def build_summary_from_file(cls, results_file: str, output_file: Optional[str] = None, stat_mode: str = "per_problem") -> Dict[str, Any]:
        return cls.build_equiv_summary(results_file=results_file, output_file=output_file, stat_mode=stat_mode)

    @classmethod
    def build_summary_from_files(cls, results_files: List[str], output_file: Optional[str] = None, stat_mode: str = "per_problem") -> Dict[str, Any]:
        return cls.build_equiv_summary(results_files=results_files, output_file=output_file, stat_mode=stat_mode)

    @classmethod
    def analyze_results_file(cls, results_file: str, stat_mode: str = "per_problem") -> Dict[str, Any]:
        summary = cls.build_equiv_summary(results_file=results_file, stat_mode=stat_mode)
        stats = summary['summary']
        print(f"\n{'='*50}")
        print(f"EQUIVALENCE CHECK SUMMARY")
        print(f"{'='*50}")
        print(f"Statistics Mode: {stats.get('stat_mode', 'per_problem')}")
        print(f"{stats.get('total_description', 'Total')}: {stats['total']}")
        print(f"Type success:   {stats['acc_type']:.2%} ({stats['acc_type']*stats['total']:.0f}/{stats['total']})")
        print(f"P→Q success:    {stats['acc_pq']:.2%} ({stats['acc_pq']*stats['total']:.0f}/{stats['total']})")
        print(f"Q→P success:    {stats['acc_qp']:.2%} ({stats['acc_qp']*stats['total']:.0f}/{stats['total']})")
        print(f"BEQ (P↔Q):      {stats['acc_beq']:.2%} ({stats['acc_beq']*stats['total']:.0f}/{stats['total']})")
        print(f"Likely BEQ:     {stats['acc_likelybeq']:.2%} ({stats['acc_likelybeq']*stats['total']:.0f}/{stats['total']})")
        print(f"{'='*50}")
        return summary

    # ---------- High-level summary table generation (Markdown/CSV/PDF) ----------
    @staticmethod
    def _parse_dirname(name: str):
        import re
        m = re.match(r"^(?P<model>.+)_(?P<stage_num>[1234])_(?P<stage_name>[A-Za-z\-]+)_(?P<knowledge>[^_]+)_(?P<nshot>[01])$", name)
        if not m:
            return None
        d = m.groupdict()
        try:
            d["stage_num"] = int(d["stage_num"])  # type: ignore
            d["nshot"] = int(d["nshot"])  # type: ignore
        except Exception:
            return None
        return d

    @staticmethod
    def _map_setting(knowledge: str, stage_num: int):
        k = (knowledge or '').lower()
        if 'oracle' in k:
            k_norm = 'Oracle'
        elif 'learn' in k:
            k_norm = 'Learned'
        elif any(tag in k for tag in ['barebone', 'barebones', 'bare', 'none', 'no', 'vanilla', 'base']):
            k_norm = 'Barebone'
        else:
            return None
        if stage_num not in {1,2,3,4}:
            return None
        return f"{k_norm} + {stage_num}-Stage"

    @classmethod
    def _load_metric_triplet(cls, merged_path: str):
        try:
            with open(merged_path, 'r', encoding='utf-8') as f:
                obj = json.load(f)
            s = obj.get('summary', {})
            type_acc = s.get('acc_type')
            likely = s.get('acc_likelybeq')
            eq = s.get('acc_beq')
            if not all(isinstance(v, (int, float)) for v in [type_acc, likely, eq]):
                return None
            return float(type_acc), float(likely), float(eq)
        except Exception:
            return None

    @classmethod
    def _collect_triplets(cls, base_dir: str):
        import os
        base_dir = os.path.abspath(base_dir)
        rows = {}
        settings_seen = set()
        try:
            for name in sorted(os.listdir(base_dir)):
                path = os.path.join(base_dir, name)
                if not os.path.isdir(path):
                    continue
                parsed = cls._parse_dirname(name)
                if not parsed:
                    continue
                merged = os.path.join(path, 'equiv_summary_merged.json')
                if not os.path.isfile(merged):
                    continue
                setting = cls._map_setting(parsed['knowledge'], parsed['stage_num'])
                if setting is None:
                    continue
                tpl = cls._load_metric_triplet(merged)
                if tpl is None:
                    continue
                key = (parsed['model'], parsed['nshot'])
                rows.setdefault(key, {})[setting] = tpl
                settings_seen.add(setting)
        except Exception:
            pass
        # consistent ordering helpers
        settings_all = []
        for K in ['Oracle', 'Learned', 'Barebone']:
            for s in (1,2,3,4):
                lab = f"{K} + {s}-Stage"
                if lab in settings_seen:
                    settings_all.append(lab)
        def model_sort_key(model: str):
            pri = 0 if model.lower().startswith('gpt') else 1
            return (pri, model.lower())
        ordered_keys = sorted(rows.keys(), key=lambda k: (model_sort_key(k[0]), k[1]))
        return rows, ordered_keys, settings_all

    @classmethod
    def write_summary_tables(cls, *, base_dir: str, mode: str = 'composite', metric: str = 'acc_likelybeq', write_pdf: bool = False) -> Dict[str, str]:
        """Generate Markdown and CSV summary tables under base_dir.

        Returns a dict with paths: {'md': ..., 'csv': ..., 'csv_grouped': ..., 'pdf': optional}
        """
        from pathlib import Path
        import csv, shutil, subprocess
        base = Path(base_dir)
        base.mkdir(parents=True, exist_ok=True)

        # Build Markdown content
        def build_table_metric(metric_name: str) -> str:
            rows, ordered_keys, settings = cls._collect_triplets(str(base))
            columns = ['Model', 'Examples', *settings]
            def format_pct(x):
                return '' if x is None else f"{x*100:.1f}%"
            # Reduce rows to single metric
            lines = [f"Metric: `{metric_name}` from `equiv_summary_merged.json`\n"]
            lines.append(' | '.join(columns))
            lines.append(' | '.join(['---']*len(columns)))
            # extract specific metric
            idx = {'acc_type':0, 'acc_likelybeq':1, 'acc_beq':2}.get(metric_name, 1)
            # values per key
            for (model, shot) in ordered_keys:
                vals = rows[(model, shot)]
                row = [model, f"{shot}-Shot"]
                for s in settings:
                    tpl = vals.get(s)
                    cell = format_pct(tpl[idx]) if tpl else ''
                    row.append(cell)
                lines.append(' | '.join(row))
            # averages
            for shot in (0,1):
                row = ['Average', f"{shot}-Shot"]
                for s in settings:
                    lst = [rows[k][s][idx] for k in ordered_keys if k[1]==shot and s in rows[k]]
                    cell = format_pct(sum(lst)/len(lst)) if lst else ''
                    row.append(cell)
                lines.append(' | '.join(row))
            return '\n'.join(lines) + '\n'

        def build_table_composite() -> str:
            rows, ordered_keys, settings = cls._collect_triplets(str(base))
            columns = ['Model','Examples',*settings]
            def fmt_triplet(t):
                if not t:
                    return ''
                t1,l1,e1 = t
                return f"{t1*100:.2f}% ({l1*100:.2f}% + {e1*100:.2f}%)"
            lines = ["Composite: type% (likely% + eq%) [percentages]\n"]
            lines.append(' | '.join(columns))
            lines.append(' | '.join(['---']*len(columns)))
            for (model, shot) in ordered_keys:
                vals = rows[(model, shot)]
                row = [model, f"{shot}-Shot"]
                for s in settings:
                    row.append(fmt_triplet(vals.get(s)))
                lines.append(' | '.join(row))
            for shot in (0,1):
                row_vals = []
                rows_map = rows
                for s in settings:
                    lst = [rows_map[k][s] for k in ordered_keys if k[1]==shot and s in rows_map[k]]
                    if lst:
                        t = (sum(v[0] for v in lst) / len(lst))
                        l = (sum(v[1] for v in lst) / len(lst))
                        e = (sum(v[2] for v in lst) / len(lst))
                        row_vals.append((t,l,e))
                    else:
                        row_vals.append(None)
                row = ['Average', f"{shot}-Shot"]
                for tpl in row_vals:
                    row.append(fmt_triplet(tpl))
                lines.append(' | '.join(row))
            return '\n'.join(lines) + '\n'

        md_out = base / 'summary_table.md'
        csv_out = base / 'summary_table.csv'
        csv_grouped = base / 'summary_table_grouped.csv'
        pdf_out = base / 'summary_table.pdf'

        md_text = build_table_composite() if mode == 'composite' else build_table_metric(metric)
        md_out.write_text(md_text, encoding='utf-8')

        # slim CSV (selected settings and renamed Barebone->None)
        def write_csv_slim():
            import csv
            rows, ordered_keys, _ = cls._collect_triplets(str(base))
            header = ['Model','Examples','Oracle + 4-Stage','Learned + 4-Stage','Learned + 1-Stage','None + 4-Stage','None + 1-Stage']
            def relabel(s):
                return s.replace('Barebone','None')
            def fmt(t):
                if not t:
                    return ''
                T,L,E = t
                return f"{T*100:.2f}% ({L*100:.2f}% + {E*100:.2f}%)"
            with open(csv_out, 'w', newline='', encoding='utf-8') as f:
                w = csv.writer(f)
                w.writerow(header)
                for (model, shot) in ordered_keys:
                    vals = rows[(model, shot)]
                    conv = {relabel(k): v for k,v in vals.items()}
                    row = [model, f"{shot}-Shot"]
                    for s in header[2:]:
                        row.append(fmt(conv.get(s)))
                    w.writerow(row)
                # averages
                for shot in (0,1):
                    row = ['Average', f"{shot}-Shot"]
                    for s in header[2:]:
                        lst = [
                            {relabel(k):v for k,v in rows[k2].items()}.get(s)
                            for k2 in ordered_keys if k2[1]==shot
                        ]
                        lst = [x for x in lst if x]
                        if lst:
                            T=sum(v[0] for v in lst)/len(lst); L=sum(v[1] for v in lst)/len(lst); E=sum(v[2] for v in lst)/len(lst)
                            row.append(fmt((T,L,E)))
                        else:
                            row.append('')
                    w.writerow(row)

        def write_csv_grouped():
            import csv
            rows, ordered_keys, settings = cls._collect_triplets(str(base))
            header = ['Model','Examples','Oracle + 4-Stage','Learned + 4-Stage','Learned + 1-Stage','Barebone + 4-Stage','Barebone + 1-Stage']
            non_reasoning = ['gpt-4o-2024-11-20','gpt-4.1-2025-04-14','gpt-4.1-mini-2025-04-14','qwen_qwen3-14b','qwen_qwen3-32b','qwen_qwen3-235b-a22b-2507']
            reasoning = ['gpt-5-2025-08-07','gpt-5-mini-2025-08-07']
            def fmt(t):
                if not t:
                    return ''
                T,L,E = t
                return f"{T*100:.2f}% ({L*100:.2f}% + {E*100:.2f}%)"
            def emit_group(w, title, models):
                w.writerow([title])
                w.writerow(header)
                for m in models:
                    for shot in (0,1):
                        key=(m,shot)
                        vals = rows.get(key, {})
                        row=[m,f"{shot}-Shot"]
                        for s in header[2:]:
                            row.append(fmt(vals.get(s)))
                        w.writerow(row)
                # averages per shot
                for shot in (0,1):
                    avg_cells=[]
                    for s in header[2:]:
                        lst=[rows.get((m,shot),{}).get(s) for m in models if s in rows.get((m,shot),{})]
                        if lst:
                            T=sum(v[0] for v in lst)/len(lst); L=sum(v[1] for v in lst)/len(lst); E=sum(v[2] for v in lst)/len(lst)
                            avg_cells.append(fmt((T,L,E)))
                        else:
                            avg_cells.append('')
                    w.writerow(['Average', f"{shot}-Shot", *avg_cells])
            with open(csv_grouped, 'w', newline='', encoding='utf-8') as f:
                w = csv.writer(f)
                emit_group(w, 'Non-Reasoning Models', non_reasoning)
                w.writerow([])
                emit_group(w, 'Reasoning Models', reasoning)

        write_csv_slim()
        write_csv_grouped()

        out = {'md': str(md_out), 'csv': str(csv_out), 'csv_grouped': str(csv_grouped)}
        if write_pdf:
            # Try optional PDF exports using available tools
            status = None
            if shutil.which('pandoc'):
                try:
                    subprocess.run(['pandoc', str(md_out), '-o', str(pdf_out), '--from', 'gfm', '--pdf-engine=xelatex'], check=True)
                    status = 'pandoc'
                except Exception:
                    status = None
            if not status and shutil.which('wkhtmltopdf'):
                try:
                    html = md_out.read_text(encoding='utf-8')
                    html_path = pdf_out.with_suffix('.html')
                    html_path.write_text(html, encoding='utf-8')
                    subprocess.run(['wkhtmltopdf', str(html_path), str(pdf_out)], check=True)
                    status = 'wkhtmltopdf'
                except Exception:
                    status = None
            if status:
                out['pdf'] = str(pdf_out)
        return out
