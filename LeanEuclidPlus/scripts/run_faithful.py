#!/usr/bin/env python3
"""run_faithful.py — headless driver for the faithful pipeline, with cost + transcript capture.

Drives Claude Code non-interactively (`claude -p`) across one or more props, one phase at a time,
saving the FULL agent trace and per-phase cost. Two unattended segments around the human review gate:

  map    split → translate → assemble → provable    (STOPS at the human GATE-A review + `--save`)
  prove  the resumable prove loop until `check_step <propdir> --all` passes

Per-prop artifacts under <propdir>/:
  runs/<phase>-<seq>-<sid>.jsonl    full streamed agent trace (git-ignored)
  cost/split.json, cost/translate.json          per-phase LLM cost totals   (committed)
  cost/prove/<seq>.json                           one checkpoint per prove session: status + cost
  cost/summary.json                               rollup: per-phase + overall + checkpoint pointers

Cost comes from the terminal `result` event of `claude -p --output-format stream-json --verbose`
(`total_cost_usd` + `usage`). Cumulative cost for a prove checkpoint = sum over that prop's prove
sessions; the delta between two checkpoints is the cost of the work between them.

Usage:
  python3 scripts/run_faithful.py map   Book1/Prop18 [Book1/Prop19 …] [--concurrency N] [--model M] [--dry-run]
  python3 scripts/run_faithful.py prove Book1/Prop18 [...] [--concurrency N] [--model M] [--max-resumes K] [--dry-run]

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
from concurrent.futures import ThreadPoolExecutor, as_completed

sys.path.insert(0, os.path.dirname(__file__))
import faithful_lib as L

REPO_ROOT = os.path.dirname(L.BOOK_ROOT)          # the DNA repo root (holds .claude/ + CLAUDE.md)
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
                   timeout=DEFAULT_TIMEOUT, dry_run=False):
    """Run one `claude -p` session. Tees every stream-json line to `transcript_path`. Returns a dict:
    {session_id, cost_usd, usage, ok, error}. On dry-run, prints the command and returns a stub."""
    cmd = ["claude", "-p", prompt, "--output-format", "stream-json", "--verbose"]
    if model:
        cmd += ["--model", model]
    if resume_sid:
        cmd += ["--resume", resume_sid]

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
    return f'"{s}"' if (" " in s or "/" in s) else s


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
    for phase in ("split", "translate"):
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


# ── segment: map (split → translate → assemble → provable) ────────────────────────────────────────
def run_map(prop, *, model=None, dry_run=False):
    propdir = _abs_propdir(prop)
    if not os.path.isdir(propdir):
        return prop, False, f"propdir not found: {prop}"
    log = [f"[map] {prop}"]

    for phase, slash in (("split", "/faithful-split"), ("translate", "/faithful-translate")):
        transcript = os.path.join(_runs_dir(propdir), f"{phase}-1.jsonl")
        res = claude_session(f"{slash} {prop}", transcript, model=model, dry_run=dry_run)
        # transcript filename gets the real session id appended once known (keeps them unique/traceable)
        if res.get("session_id") and not dry_run:
            newt = os.path.join(_runs_dir(propdir), f"{phase}-1-{res['session_id']}.jsonl")
            try:
                os.replace(transcript, newt)
            except OSError:
                pass
        if not dry_run:
            _write_json(os.path.join(_cost_dir(propdir), f"{phase}.json"),
                        {"phase": phase, "session_id": res.get("session_id"),
                         "model": res.get("model"),
                         "cost_usd": res.get("cost_usd"), "usage": res.get("usage")})
        log.append(f"  {phase}: {'ok' if res['ok'] else 'FAIL — ' + str(res['error'])}"
                   f"  ${res.get('cost_usd') or 0:.4f}")
        if not res["ok"]:
            if not dry_run:
                _rollup_summary(propdir)
            return prop, False, "\n".join(log)
        # FAIL-FAST: the phase's product must exist before we pay for the next phase. A missing
        # split.json/translate.json almost always means the agent's Write was blocked (e.g. no
        # `Write(LeanEuclidPlus/Book1/**)` permission) — abort now instead of running translate/assemble.
        product = os.path.join(propdir, f"{phase}.json")
        if not dry_run and not os.path.exists(product):
            log.append(f"  {phase}: FAIL — {phase}.json was NOT written to disk. The agent's Write was "
                       f"likely blocked — confirm settings.json allows `Write(LeanEuclidPlus/Book1/**)` / "
                       f"`Edit(LeanEuclidPlus/Book1/**)`. Aborting {prop} (not paying for the next phase).")
            _rollup_summary(propdir)
            return prop, False, "\n".join(log)

    # assemble (deterministic, no LLM)
    if not _run_script(["scripts/faithful_map_assemble.py", prop], dry_run, log, "assemble"):
        _rollup_summary(propdir)
        return prop, False, "\n".join(log)
    # provable + faithful text check (deterministic)
    ok_p = _run_script(["scripts/check_step.py", prop, "--provable"], dry_run, log, "provable")
    ok_f = _run_script(["scripts/check_faithful.py", f"{prop}/Main.lean"], dry_run, log, "check_faithful")

    if not dry_run:
        _rollup_summary(propdir)
    log.append("  → STOP: human GATE-A (review the map, then `check_steps.py --save`).")
    return prop, (ok_p and ok_f), "\n".join(log)


# ── segment: prove (resumable loop until check_step --all passes) ─────────────────────────────────
def run_prove(prop, *, model=None, max_resumes=6, dry_run=False):
    propdir = _abs_propdir(prop)
    if not os.path.isdir(propdir):
        return prop, False, f"propdir not found: {prop}"
    log = [f"[prove] {prop}"]

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
                      f"--all` exits 0. Do NOT stop to ask; keep decomposing and proving.{ref_note}")
        else:
            prompt = (f"/faithful-prove {prop}  — CONTINUE a partially-finished proof from a previous "
                      f"session. Already-certified nodes are recorded on disk; run "
                      f"`python3 scripts/check_step.py {prop} --status` (or `--drive`) to see what's "
                      f"still todo/stale and pick up there. Work until "
                      f"`python3 scripts/check_step.py {prop} --all` exits 0. Do NOT stop to ask.{ref_note}")
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

        if dry_run:
            break
        if all_done:
            # status says ready → confirm ONCE with the authoritative --all (per the methodology).
            ok_all = _run_script(["scripts/check_step.py", prop, "--all"], False, log, "check_step --all")
            if ok_all:
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
    ap.add_argument("segment", choices=["map", "prove"], help="which unattended segment to run")
    ap.add_argument("props", nargs="+", help="prop dirs, e.g. Book1/Prop18 Book1/Prop19")
    ap.add_argument("--concurrency", type=int, default=4, help="max props in flight (default 4)")
    ap.add_argument("--model", default=None, help="override the claude model (default: session default)")
    ap.add_argument("--max-resumes", type=int, default=6, help="prove: max resume sessions per prop")
    ap.add_argument("--dry-run", action="store_true", help="print the plan; spawn nothing")
    args = ap.parse_args()

    fn = (lambda p: run_map(p, model=args.model, dry_run=args.dry_run)) if args.segment == "map" \
        else (lambda p: run_prove(p, model=args.model, max_resumes=args.max_resumes, dry_run=args.dry_run))

    results = []
    with ThreadPoolExecutor(max_workers=max(1, args.concurrency)) as pool:
        futs = {pool.submit(fn, p): p for p in args.props}
        for fut in as_completed(futs):
            prop, ok, report = fut.result()
            print(report)
            print()
            results.append((prop, ok))

    print("=" * 60)
    for prop, ok in sorted(results):
        print(f"  {'✓' if ok else '✗'}  {prop}")
    n_ok = sum(1 for _, ok in results if ok)
    print(f"{n_ok}/{len(results)} {args.segment} segments succeeded.")
    sys.exit(0 if n_ok == len(results) else 1)


if __name__ == "__main__":
    main()
