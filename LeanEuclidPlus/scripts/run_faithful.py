#!/usr/bin/env python3
"""run_faithful.py — headless driver for the faithful pipeline, with cost + transcript capture.

Drives Claude Code non-interactively (`claude -p`) across one or more props, one phase at a time,
saving the FULL agent trace and per-phase cost. Segments around the human review gate:

  map        split → translate → assemble → review → provable    (STOPS at the human GATE-A + `--save`)
  split      just the split stage        (re-run ONE Phase-A stage in isolation)
  translate  just translate (+ assemble + provable check)
  assemble   just assemble (+ provable check)  — deterministic, no LLM
  review     just the review stage (forced) (+ provable check)   — e.g. re-review after fixing a claim
  prove      the resumable prove loop until `check_step <propdir> --all` passes

Per-prop artifacts under <propdir>/:
  runs/<phase>-<seq>-<sid>.jsonl    full streamed agent trace (git-ignored)
  cost/split.json, cost/translate.json, cost/review.json   per-phase LLM cost totals  (committed)
  cost/prove/<seq>.json                           one checkpoint per prove session: status + cost
  cost/summary.json                               rollup: per-phase + overall + checkpoint pointers

Cost comes from the terminal `result` event of `claude -p --output-format stream-json --verbose`
(`total_cost_usd` + `usage`). Cumulative cost for a prove checkpoint = sum over that prop's prove
sessions; the delta between two checkpoints is the cost of the work between them.

Usage:
  python3 scripts/run_faithful.py map    Book1/Prop18 [Book1/Prop19 …] [--concurrency N] [--model M] [--dry-run]
  python3 scripts/run_faithful.py review Book1/Prop08 [...]   # re-run just one Phase-A stage
  python3 scripts/run_faithful.py prove  Book1/Prop18 [...] [--concurrency N] [--model M] [--max-resumes K] [--dry-run]
  (single-stage segments: split | translate | assemble | review — same flags as `map`)

⚠ HUMAN-run orchestrator — it SPAWNS `claude`. Run it OUTSIDE an agent session (the agent build
sandbox hard-denies spawning `claude`). Between `map` and `prove` you review each map and run
`python3 scripts/check_steps.py --save <propdir>/Main.lean` (human-only gate). After `prove` passes,
Phase C (`wire_main.py` + aggregator import + checks) is the mechanical human step.
"""
import argparse
import json
import os
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed

sys.path.insert(0, os.path.dirname(__file__))
import faithful_lib as L

REPO_ROOT = os.path.dirname(L.BOOK_ROOT)          # the DNA repo root (holds .claude/ + CLAUDE.md)
REG_DIR = os.path.join(L.BOOK_ROOT, ".lake", "faithful_runs")   # live-run registry (git-ignored)

# Per-invocation HARD restriction for the MAP phases split + translate ONLY: those never need axioms,
# so deny reading SystemE and using find.py to surface axiom signatures. Merges with project settings
# (deny wins) for that one `claude -p` only. The REVIEW phase is NOT restricted — it may read SystemE
# signatures + find.py to confirm the faithful surface form of the few nontrivial claim types (guardrail
# in faithful-review/SKILL.md: signatures confirm surface form, never reshape a claim). prove is also
# unrestricted (it needs both).
MAP_DENY = ('{"permissions":{"deny":['
            '"Read(SystemE/**)","Read(LeanEuclidPlus/SystemE/**)",'
            '"Bash(python3 scripts/find.py:*)","Bash(python scripts/find.py:*)"]}}')
MAP_RESTRICT = ["--settings", MAP_DENY]


def _registry_write(segment, props):
    """Announce this batch so `monitor_tui.py` can auto-discover what's running (read-only). One file
    per pid; removed on exit. Best-effort — never let registry I/O break a run."""
    try:
        os.makedirs(REG_DIR, exist_ok=True)
        with open(os.path.join(REG_DIR, f"{os.getpid()}.json"), "w", encoding="utf-8") as f:
            json.dump({"pid": os.getpid(), "segment": segment, "props": props, "started": time.time()}, f)
    except OSError:
        pass


def _registry_clear():
    try:
        os.remove(os.path.join(REG_DIR, f"{os.getpid()}.json"))
    except OSError:
        pass
DEFAULT_TIMEOUT = 3 * 60 * 60                       # 3h per session wall (a prove session can be long)


# ── low-level: run one headless claude session, tee the trace, extract cost ───────────────────────
def _extract_cost(obj, acc):
    """Fold a stream-json event into the running (session_id, cost_usd, usage, model) accumulator."""
    if not isinstance(obj, dict):
        return
    if obj.get("session_id"):
        acc["session_id"] = obj["session_id"]
    # total_cost_usd may sit at top level, under `usage`, or under `cost` depending on CLI version.
    for holder in (obj, obj.get("usage") or {}, obj.get("cost") or {}):
        if isinstance(holder, dict) and holder.get("total_cost_usd") is not None:
            acc["cost_usd"] = holder["total_cost_usd"]
    if isinstance(obj.get("usage"), dict):
        acc["usage"] = obj["usage"]
    # model appears on the init/system event and on assistant message events.
    m = obj.get("model") or (obj.get("message") or {}).get("model")
    if m:
        acc["model"] = m


def claude_session(prompt, transcript_path, *, model=None, resume_sid=None,
                   timeout=DEFAULT_TIMEOUT, dry_run=False, extra_args=None):
    """Run one `claude -p` session. Tees every stream-json line to `transcript_path`. Returns a dict:
    {session_id, cost_usd, usage, ok, error}. On dry-run, prints the command and returns a stub.
    `extra_args` appends raw CLI flags (e.g. per-invocation `--settings` deny rules)."""
    # acceptEdits: headless has no human to grant an Edit/Write prompt. The `Edit/Write(LeanEuclidPlus/
    # Book*/**)` allow-globs are written relative to the DNA repo root, but the agent runs scripts from
    # …/DNA/LeanEuclidPlus (scripts live there), so a relative glob can miss and the write is auto-denied.
    # acceptEdits auto-accepts file edits regardless; deny rules (signature JSONs, git, lake) + the
    # bash/step hooks still apply. (Bash script calls match the settings allow by command string, cwd-
    # independent, so only Edit/Write needed this.)
    cmd = ["claude", "-p", prompt, "--output-format", "stream-json", "--verbose",
           "--permission-mode", "acceptEdits"]
    if model:
        cmd += ["--model", model]
    if resume_sid:
        cmd += ["--resume", resume_sid]
    if extra_args:
        cmd += extra_args

    if dry_run:
        print(f"    [dry-run] (cwd={REPO_ROOT}) {' '.join(_shquote(c) for c in cmd)}")
        print(f"    [dry-run] trace → {os.path.relpath(transcript_path, L.BOOK_ROOT)}")
        return {"session_id": None, "cost_usd": 0.0, "usage": {}, "ok": True, "error": None}

    os.makedirs(os.path.dirname(transcript_path), exist_ok=True)
    acc = {"session_id": resume_sid, "cost_usd": None, "usage": {}, "model": None}
    try:
        with open(transcript_path, "w", encoding="utf-8") as trace:
            proc = subprocess.Popen(cmd, cwd=REPO_ROOT, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, text=True, bufsize=1)
            # Watchdog: kill the session if it exceeds `timeout` even while blocked reading stdout
            # (a stdout-hang would otherwise wedge this pool worker forever at high concurrency).
            timed_out = {"hit": False}

            def _kill():
                timed_out["hit"] = True
                proc.kill()
            wd = threading.Timer(timeout, _kill)
            wd.start()
            try:
                assert proc.stdout is not None                  # guaranteed by stdout=PIPE
                for line in proc.stdout:
                    trace.write(line)
                    trace.flush()
                    s = line.strip()
                    if s.startswith("{"):
                        try:
                            _extract_cost(json.loads(s), acc)
                        except ValueError:
                            pass
                rc = proc.wait()
            finally:
                wd.cancel()
            if timed_out["hit"]:
                return {**acc, "ok": False, "error": f"timeout after {timeout}s"}
    except FileNotFoundError:
        return {**acc, "ok": False, "error": "`claude` CLI not found on PATH"}
    return {**acc, "ok": rc == 0, "error": None if rc == 0 else f"claude exited {rc}"}


def _shquote(s):
    if any(c in s for c in ' "{}()') and "'" not in s:      # JSON / spaces → single-quote for display
        return f"'{s}'"
    if " " in s or "/" in s:
        return f'"{s}"'
    return s


# ── artifact paths ────────────────────────────────────────────────────────────────────────────────
def _abs_propdir(prop):
    return os.path.join(L.BOOK_ROOT, prop) if not os.path.isabs(prop) else prop


def _cost_dir(propdir):
    return os.path.join(propdir, "cost")


def _runs_dir(propdir):
    return os.path.join(propdir, "runs")


def _write_json(path, obj):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(obj, f, indent=2, sort_keys=True)
        f.write("\n")
    os.replace(tmp, path)


def _status_snapshot(propdir):
    """Serializable status via faithful_lib.status_rows (read-only; no builds). Returns
    (snapshot_dict, all_done_bool)."""
    rows, checks = L.status_rows(propdir)
    all_done = (bool(rows) and all(st == "done" for _, st, _ in rows)
                and not checks.get("error")
                and checks.get("deps") and checks.get("integrity")
                and not checks.get("orphans"))
    snap = {"nodes": [{"name": n, "state": st, "detail": d} for n, st, d in rows],
            "checks": checks}
    return snap, all_done


def _rollup_summary(propdir):
    """Roll every cost/*.json into cost/summary.json (per-phase totals + overall + checkpoint list)."""
    cost_dir = _cost_dir(propdir)
    summary = {"prop": os.path.relpath(propdir, L.BOOK_ROOT), "phases": {}, "total_usd": 0.0,
               "prove_checkpoints": []}
    for phase in ("split", "translate", "review"):
        p = os.path.join(cost_dir, f"{phase}.json")
        if os.path.exists(p):
            rec = json.load(open(p, encoding="utf-8"))
            summary["phases"][phase] = rec.get("cost_usd", 0.0)
            summary["total_usd"] += rec.get("cost_usd", 0.0) or 0.0
    prove_dir = os.path.join(cost_dir, "prove")
    prove_total = 0.0
    if os.path.isdir(prove_dir):
        for fn in sorted(os.listdir(prove_dir), key=L.natural_key):
            if not fn.endswith(".json"):
                continue
            rec = json.load(open(os.path.join(prove_dir, fn), encoding="utf-8"))
            summary["prove_checkpoints"].append(f"cost/prove/{fn}")
            prove_total = max(prove_total, rec.get("cumulative_usd", 0.0) or 0.0)
    if os.path.isdir(prove_dir):
        summary["phases"]["prove"] = prove_total
        summary["total_usd"] += prove_total
    _write_json(os.path.join(cost_dir, "summary.json"), summary)
    return summary


def _needs_human(propdir):
    """True if the agent left a NEEDS_HUMAN.md — it hit a decision only a human can make."""
    return os.path.exists(os.path.join(propdir, "NEEDS_HUMAN.md"))


def _clear_needs_human(propdir):
    """Remove a stale NEEDS_HUMAN.md at the start of a (re)run — re-running means 'try again', and a
    fresh attempt re-creates it only if the blocker genuinely persists."""
    try:
        os.remove(os.path.join(propdir, "NEEDS_HUMAN.md"))
    except OSError:
        pass


def _translate_flags(propdir):
    """Entries in translate.json carrying an `"issue"` (structural frame) or a `"review_note"` — the
    review stage's work-list hints. Informational for the driver (review ALWAYS runs and self-triages);
    used only to log how many flags await."""
    try:
        data = json.load(open(os.path.join(propdir, "translate.json"), encoding="utf-8"))
    except (ValueError, OSError):
        return []
    if not isinstance(data, list):
        return []
    return [e for e in data if isinstance(e, dict) and (e.get("issue") or e.get("review_note"))]


def _headless_note(prop):
    """Appended to every phase prompt: headless agents can't be asked, so route GENUINE blockers to a
    file and stop — the point is to halt cleanly on real problems without thrashing/burning tokens."""
    return (f" You are running HEADLESS — there is NO interactive human, so do NOT call "
            f"AskUserQuestion (it cannot be answered; the session just ends). STOP cleanly by writing a "
            f"short, specific note to {prop}/NEEDS_HUMAN.md when — and only when — you hit a GENUINE "
            f"blocker: a decision only a human can make (a faithful modeling choice the vocabulary "
            f"can't express), a claim/map that looks WRONG or unprovable, or you are truly stuck on a "
            f"node after honest attempts. In those cases write the note and STOP — do NOT thrash, "
            f"force a tactic, or keep retrying; that just burns tokens. (Being merely HARD is not a "
            f"blocker — decompose and continue.)")


# ── Phase-A stages (each callable on its own; `map` runs them in sequence) ──────────────────────────
def _stage_text(prop, propdir, phase, slash, *, model, dry_run, log):
    """One TEXT stage — split or translate — run under MAP_RESTRICT (no SystemE/find.py). Spawns the
    agent, saves cost, renames the transcript, then fail-fast checks (agent ok? NEEDS_HUMAN? product on
    disk?). Returns (ok, stop): stop=True means the pipeline must abort here."""
    transcript = os.path.join(_runs_dir(propdir), f"{phase}-1.jsonl")
    res = claude_session(f"{slash} {prop}{_headless_note(prop)}", transcript,
                         model=model, dry_run=dry_run, extra_args=MAP_RESTRICT)
    # transcript filename gets the real session id appended once known (keeps them unique/traceable)
    if res.get("session_id") and not dry_run:
        newt = os.path.join(_runs_dir(propdir), f"{phase}-1-{res['session_id']}.jsonl")
        try:
            os.replace(transcript, newt)
        except OSError:
            pass
    if not dry_run:
        _write_json(os.path.join(_cost_dir(propdir), f"{phase}.json"),
                    {"phase": phase, "session_id": res.get("session_id"), "model": res.get("model"),
                     "cost_usd": res.get("cost_usd"), "usage": res.get("usage")})
    log.append(f"  {phase}: {'ok' if res['ok'] else 'FAIL — ' + str(res['error'])}"
               f"  ${res.get('cost_usd') or 0:.4f}")
    if not res["ok"]:
        return False, True
    # Agent flagged a human-decision blocker (checked BEFORE the product check, so we don't
    # misreport a deliberate NEEDS_HUMAN stop as a write-permission failure).
    if not dry_run and _needs_human(propdir):
        log.append(f"  {phase}: ⚠ BLOCKED — agent wrote {prop}/NEEDS_HUMAN.md (human decision "
                   f"needed). Read it, resolve, delete it, then re-run.")
        return False, True
    # FAIL-FAST: the phase's product must exist before we pay for the next phase. A missing
    # split.json/translate.json almost always means the agent's Write was blocked (e.g. no
    # `Write(LeanEuclidPlus/Book1/**)` permission) — abort now instead of running translate/assemble.
    if not dry_run and not os.path.exists(os.path.join(propdir, f"{phase}.json")):
        log.append(f"  {phase}: FAIL — {phase}.json was NOT written to disk. The agent's Write was "
                   f"likely blocked — confirm settings.json allows `Write(LeanEuclidPlus/Book1/**)` / "
                   f"`Edit(LeanEuclidPlus/Book1/**)`. Aborting {prop} (not paying for the next phase).")
        return False, True
    # SPLIT TILING GATE (fail-fast): don't pay for translate on a split that doesn't reproduce the
    # canonical text byte-for-byte. The split agent is told to make this PASS itself; this is the
    # deterministic backstop. (Only runs for the split phase.)
    if not dry_run and phase == "split" and not _run_script(
            ["scripts/check_faithful.py", "--split", prop], dry_run, log, "split-tiling"):
        log.append(f"  split: FAIL — split.json does not tile the canonical text (see --split output "
                   f"above). Re-run split; the agent must loop `--split` to PASS. Aborting {prop}.")
        return False, True
    return True, False


def _stage_scaffold_translate(prop, *, dry_run, log):
    """Deterministic (no LLM): stamp the translate.json SKELETON from split.json before the translate
    agent runs — so the agent only FILLS claim slots, never re-keys indices or re-copies text."""
    return _run_script(["scripts/scaffold_translate.py", prop, "--force"], dry_run, log, "scaffold-translate")


def _stage_assemble(prop, *, dry_run, log):
    """Deterministic assemble (no LLM): translate.json → Main.lean. Returns ok."""
    return _run_script(["scripts/faithful_map_assemble.py", prop], dry_run, log, "assemble")


def _stage_review(prop, propdir, *, model, dry_run, log, force=False):
    """Review — ALWAYS runs (the skill self-triages). It runs check_faithful + check_step --provable,
    builds a work-list from translate.json's `"issue"`/`"review_note"` flags + any check failure, and
    CHEAP-EXITS without a deep-dive when that list is empty and both checks are green; otherwise it edits
    Main.lean to GREEN. NOT under MAP_RESTRICT (may read SystemE + find.py for surface-form confirmation).
    `force` is retained for the `review` segment but no longer gates anything. Returns (ran, stop):
    stop=True ⟹ a NEEDS_HUMAN block, abort."""
    if dry_run:
        log.append("  review: [dry-run] (always runs; the skill cheap-exits when the map is clean)")
        return False, False
    n_issues = sum(1 for e in _translate_flags(propdir) if e)   # informational only; review always runs
    if n_issues:
        log.append(f"  review: {n_issues} flag(s) in translate.json to resolve")
    transcript = os.path.join(_runs_dir(propdir), "review-1.jsonl")
    res = claude_session(f"/faithful-review {prop}{_headless_note(prop)}", transcript, model=model)
    if res.get("session_id"):
        newt = os.path.join(_runs_dir(propdir), f"review-1-{res['session_id']}.jsonl")
        try:
            os.replace(transcript, newt)
        except OSError:
            pass
    _write_json(os.path.join(_cost_dir(propdir), "review.json"),
                {"phase": "review", "session_id": res.get("session_id"), "model": res.get("model"),
                 "cost_usd": res.get("cost_usd"), "usage": res.get("usage")})
    log.append(f"  review: {'ok' if res['ok'] else 'FAIL — ' + str(res['error'])}"
               f"  ${res.get('cost_usd') or 0:.4f}")
    if _needs_human(propdir):
        log.append(f"  ⚠ BLOCKED — review wrote {prop}/NEEDS_HUMAN.md (a flag it couldn't resolve "
                   f"even with reference props + signatures). Read it, resolve, delete it, then re-run.")
        return True, True
    return True, False


def _stage_checks(prop, *, dry_run, log):
    """provable (Main elaborates, all-sorry) + check_faithful (text tiling + deps + the no-`True` gate).
    Returns ok."""
    ok_p = _run_script(["scripts/check_step.py", prop, "--provable"], dry_run, log, "provable")
    ok_f = _run_script(["scripts/check_faithful.py", f"{prop}/Main.lean"], dry_run, log, "check_faithful")
    return ok_p and ok_f


# ── segment: map (split → translate → assemble → review → provable) ────────────────────────────────
def run_map(prop, *, model=None, dry_run=False):
    propdir = _abs_propdir(prop)
    if not os.path.isdir(propdir):
        return prop, False, f"propdir not found: {prop}"
    log = [f"[map] {prop}"]
    if not dry_run:
        _clear_needs_human(propdir)   # a (re)run starts fresh; review re-creates it if still stuck

    ok, stop = _stage_text(prop, propdir, "split", "/faithful-split", model=model, dry_run=dry_run, log=log)
    if stop:
        if not dry_run:
            _rollup_summary(propdir)
        return prop, False, "\n".join(log)

    # Deterministic: stamp the translate.json skeleton from split.json BEFORE the translate agent.
    if not _stage_scaffold_translate(prop, dry_run=dry_run, log=log):
        if not dry_run:
            _rollup_summary(propdir)
        return prop, False, "\n".join(log)

    ok, stop = _stage_text(prop, propdir, "translate", "/faithful-translate", model=model, dry_run=dry_run, log=log)
    if stop:
        if not dry_run:
            _rollup_summary(propdir)
        return prop, False, "\n".join(log)

    if not _stage_assemble(prop, dry_run=dry_run, log=log):
        if not dry_run:
            _rollup_summary(propdir)
        return prop, False, "\n".join(log)

    _, stop = _stage_review(prop, propdir, model=model, dry_run=dry_run, log=log)
    if stop:
        _rollup_summary(propdir)
        return prop, False, "\n".join(log)

    ok = _stage_checks(prop, dry_run=dry_run, log=log)
    if not dry_run:
        _rollup_summary(propdir)
    log.append("  → STOP: human GATE-A (review the map, then `check_steps.py --save`).")
    return prop, ok, "\n".join(log)


# ── single-stage segments (run ONE Phase-A stage, e.g. re-run just `review`) ────────────────────────
def run_split(prop, *, model=None, dry_run=False):
    propdir = _abs_propdir(prop)
    if not os.path.isdir(propdir):
        return prop, False, f"propdir not found: {prop}"
    log = [f"[split] {prop}"]
    if not dry_run:
        _clear_needs_human(propdir)
    ok, _ = _stage_text(prop, propdir, "split", "/faithful-split", model=model, dry_run=dry_run, log=log)
    if not dry_run:
        _rollup_summary(propdir)
    log.append("  → next (INTERACTIVE, by hand): `/faithful-map <propdir>` — Phase-A mapping is no "
               "longer headless. Then `/faithful-prove` (or `run_faithful.py prove`).")
    return prop, ok, "\n".join(log)


def run_translate(prop, *, model=None, dry_run=False):
    propdir = _abs_propdir(prop)
    if not os.path.isdir(propdir):
        return prop, False, f"propdir not found: {prop}"
    log = [f"[translate] {prop}"]
    if not dry_run:
        _clear_needs_human(propdir)
    # Deterministic: (re)stamp the translate.json skeleton from split.json before the agent fills it.
    if not _stage_scaffold_translate(prop, dry_run=dry_run, log=log):
        if not dry_run:
            _rollup_summary(propdir)
        log.append("  → scaffold failed (is split.json present + `--split`-clean?). Run split first.")
        return prop, False, "\n".join(log)
    ok, _ = _stage_text(prop, propdir, "translate", "/faithful-translate", model=model, dry_run=dry_run, log=log)
    if ok:
        # translate's contract is to hand off a freshly-assembled Main — do the deterministic assemble
        # here so a following `review` reads an up-to-date Main.lean.
        _stage_assemble(prop, dry_run=dry_run, log=log)
        _stage_checks(prop, dry_run=dry_run, log=log)
    if not dry_run:
        _rollup_summary(propdir)
    log.append("  → next: `run_faithful.py review` (if `issue` flags) then GATE-A")
    return prop, ok, "\n".join(log)


def run_assemble(prop, *, model=None, dry_run=False):
    propdir = _abs_propdir(prop)
    if not os.path.isdir(propdir):
        return prop, False, f"propdir not found: {prop}"
    log = [f"[assemble] {prop}"]
    ok = _stage_assemble(prop, dry_run=dry_run, log=log)
    if ok:
        ok = _stage_checks(prop, dry_run=dry_run, log=log)
    if not dry_run:
        _rollup_summary(propdir)
    return prop, ok, "\n".join(log)


def run_review(prop, *, model=None, dry_run=False):
    propdir = _abs_propdir(prop)
    if not os.path.isdir(propdir):
        return prop, False, f"propdir not found: {prop}"
    log = [f"[review] {prop}"]
    if not dry_run:
        _clear_needs_human(propdir)
    # Force it: the human explicitly asked for review (the skill self-guards if there's nothing to do).
    _, stop = _stage_review(prop, propdir, model=model, dry_run=dry_run, log=log, force=True)
    ok = (not stop) and _stage_checks(prop, dry_run=dry_run, log=log)
    if not dry_run:
        _rollup_summary(propdir)
    log.append("  → STOP: human GATE-A (review the map, then `check_steps.py --save`).")
    return prop, ok, "\n".join(log)


# ── segment: prove (resumable loop until check_step --all passes) ─────────────────────────────────
def run_prove(prop, *, model=None, max_resumes=6, dry_run=False):
    propdir = _abs_propdir(prop)
    if not os.path.isdir(propdir):
        return prop, False, f"propdir not found: {prop}"
    log = [f"[prove] {prop}"]
    if not dry_run:
        _clear_needs_human(propdir)   # re-running prove means 'try again'; agent re-flags if still stuck

    # The original (non-faithful) proof, offered as a math reference (NOT a template to copy).
    bk, pn = L.book_num(propdir), L.prop_num(propdir)
    ref = f"Book/Prop{pn:02d}.lean" if bk == 1 else None
    ref_note = ("" if not ref else
                f" The original (non-faithful) proof at `{ref}` is available as a REFERENCE for the "
                f"mathematical approach — consult it so you don't rederive the geometry. But it is ONLY "
                f"a template: do NOT copy its structure or tactics. This is a fresh FAITHFUL proof "
                f"(one backing file per sentence, decomposed until every build is ≤30s).")

    prove_dir = os.path.join(_cost_dir(propdir), "prove")
    seq = len([f for f in os.listdir(prove_dir) if f.endswith(".json")]) if os.path.isdir(prove_dir) else 0
    cumulative = 0.0
    if seq and not dry_run:                                    # resume: carry prior cumulative
        prev = json.load(open(os.path.join(prove_dir, f"{seq}.json"), encoding="utf-8"))
        cumulative = prev.get("cumulative_usd", 0.0) or 0.0
    sid = None
    ok_all = False
    prev_done, stall, STALL_LIMIT = -1, 0, 2   # stop if 2 sessions in a row certify NO new node

    for attempt in range(max_resumes + 1):
        seq += 1
        transcript = os.path.join(_runs_dir(propdir), f"prove-{seq}.jsonl")
        # Each continuation is a FRESH agent (new context) — NOT a `--resume` of the prior session.
        # By this point a resumed session's context would be huge/expensive; a fresh session instead
        # re-reads the on-disk state (certified step files + `check_step --status`/`--drive`) and picks
        # up where the last one left off, skipping already-`done` nodes. Progress lives on disk, not in
        # any one session's context.
        if attempt == 0:
            prompt = (f"/faithful-prove {prop}  — work until `python3 scripts/check_step.py {prop} "
                      f"--all` exits 0. Do NOT stop to ask; keep decomposing and proving.{ref_note}"
                      f"{_headless_note(prop)}")
        else:
            prompt = (f"/faithful-prove {prop}  — CONTINUE a partially-finished proof from a previous "
                      f"session. Already-certified nodes are recorded on disk; run "
                      f"`python3 scripts/check_step.py {prop} --status` (or `--drive`) to see what's "
                      f"still todo/stale and pick up there. Work until "
                      f"`python3 scripts/check_step.py {prop} --all` exits 0. Do NOT stop to ask.{ref_note}"
                      f"{_headless_note(prop)}")
        res = claude_session(prompt, transcript, model=model, dry_run=dry_run)   # fresh session, no --resume

        if res.get("session_id"):
            sid = res["session_id"]
            if not dry_run:
                newt = os.path.join(_runs_dir(propdir), f"prove-{seq}-{sid}.jsonl")
                try:
                    os.replace(transcript, newt)
                except OSError:
                    pass
        cumulative += res.get("cost_usd") or 0.0

        # checkpoint: cheap read-only status (no builds) + cumulative cost
        if dry_run:
            snap, all_done = {"nodes": [], "checks": {}}, False
        else:
            snap, all_done = _status_snapshot(propdir)
        if not dry_run:
            _write_json(os.path.join(prove_dir, f"{seq}.json"),
                        {"seq": seq, "session_id": sid, "model": res.get("model"),
                         "this_session_usd": res.get("cost_usd"),
                         "cumulative_usd": cumulative, "status": snap})
        log.append(f"  session {seq}: {'ok' if res['ok'] else 'FAIL ' + str(res['error'])}"
                   f"  ${res.get('cost_usd') or 0:.4f}  (cum ${cumulative:.4f})"
                   f"  all_done={all_done}")

        if not dry_run and _needs_human(propdir):
            log.append(f"  ⚠ BLOCKED — {prop}/NEEDS_HUMAN.md written (human decision needed); "
                       f"stopping the resume loop. Read it, resolve, delete it, then re-run prove.")
            break

        if dry_run:
            break
        if all_done:
            # status says ready → confirm ONCE with the authoritative --all (per the methodology).
            ok_all = _run_script(["scripts/check_step.py", prop, "--all"], False, log, "check_step --all")
            if ok_all:
                break
        # STALL GUARD (objective anti-thrash): a session that certifies NO new node made no forward
        # progress. Stop resuming after STALL_LIMIT such sessions in a row — don't burn the full
        # resume budget on a stuck prop. (A prop that's progressing resets the counter every session.)
        done = sum(1 for n in snap.get("nodes", []) if n.get("state") == "done")
        stall = stall + 1 if done <= prev_done else 0
        prev_done = max(prev_done, done)
        if stall >= STALL_LIMIT:
            log.append(f"  ⚠ STALLED — {stall} sessions with no newly-certified node ({done} done). "
                       f"Stopping to avoid burning tokens; inspect `--status`/the latest trace (or the "
                       f"agent may have hit something worth a NEEDS_HUMAN note), fix, then re-run prove.")
            break
        if not res["ok"]:
            log.append("  (session failed; resuming)" if attempt < max_resumes else "  (out of resumes)")

    if not dry_run:
        _rollup_summary(propdir)
    verdict = "CERTIFIED (--all green)" if ok_all else "INCOMPLETE — inspect the latest trace / --status"
    log.append(f"  → {verdict}")
    return prop, ok_all, "\n".join(log)


def _run_script(args, dry_run, log, label):
    """Run a deterministic pipeline script (python3 scripts/…). Returns True on exit 0."""
    cmd = [sys.executable] + args
    if dry_run:
        log.append(f"  {label}: [dry-run] {' '.join(_shquote(c) for c in cmd)}")
        return True
    r = subprocess.run(cmd, cwd=L.BOOK_ROOT, capture_output=True, text=True)
    ok = r.returncode == 0
    tail = (r.stdout.strip().splitlines() or [""])[-1]
    log.append(f"  {label}: {'ok' if ok else 'FAIL(' + str(r.returncode) + ')'}  {tail[:120]}")
    return ok


# ── CLI ───────────────────────────────────────────────────────────────────────────────────────────
def main():
    ap = argparse.ArgumentParser(description="Headless faithful-pipeline driver (cost + trace capture).")
    ap.add_argument("segment", choices=["split", "prove"],
                    help="split = Phase-A text split (→ split.json, gated by --split); prove = Phase B. "
                         "(Phase-A mapping is now INTERACTIVE via /faithful-split → /faithful-map — not "
                         "headless here.)")
    ap.add_argument("props", nargs="+", help="prop dirs, e.g. Book1/Prop18 Book1/Prop19")
    ap.add_argument("--concurrency", type=int, default=4, help="max props in flight (default 4)")
    ap.add_argument("--model", default=None, help="override the claude model (default: session default)")
    ap.add_argument("--max-resumes", type=int, default=6, help="prove: max resume sessions per prop")
    ap.add_argument("--dry-run", action="store_true", help="print the plan; spawn nothing")
    args = ap.parse_args()

    runners = {
        "split": lambda p: run_split(p, model=args.model, dry_run=args.dry_run),
        "prove": lambda p: run_prove(p, model=args.model, max_resumes=args.max_resumes, dry_run=args.dry_run),
    }
    fn = runners[args.segment]

    if not args.dry_run:
        _registry_write(args.segment, args.props)
        print("Monitor live in another terminal:  python3 scripts/monitor_tui.py")
    results = []
    try:
        with ThreadPoolExecutor(max_workers=max(1, args.concurrency)) as pool:
            futs = {pool.submit(fn, p): p for p in args.props}
            for fut in as_completed(futs):
                prop, ok, report = fut.result()
                print(report)
                print()
                results.append((prop, ok))
    finally:
        _registry_clear()

    print("=" * 60)
    for prop, ok in sorted(results):
        print(f"  {'✓' if ok else '✗'}  {prop}")
    n_ok = sum(1 for _, ok in results if ok)
    print(f"{n_ok}/{len(results)} {args.segment} segments succeeded.")
    sys.exit(0 if n_ok == len(results) else 1)


if __name__ == "__main__":
    main()
