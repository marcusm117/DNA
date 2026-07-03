#!/usr/bin/env python3
"""run_faithful.py — headless batch driver for the two AUTOMATABLE faithful-pipeline phases.

Everything else in the pipeline is MANUAL (interactive by hand): `/faithful-split`, `/faithful-map`,
the human GATE-A review + `check_steps.py --save`, and Phase C (`wire_main.py`). Only two phases are
worth batching headless across many props — and this driver does exactly those two, nothing else:

  assumptions   spawn `/faithful-assumptions <prop>` per prop (runs `scripts/assumptions.py`, and the
                agent fixes any `wlog` frame break itself). Run AFTER Phase-A map + human `--save`,
                BEFORE prove.
  prove         the resumable Phase-B loop until `check_step <propdir> --all` exits 0. For a Book-1
                prop the original (non-faithful) `Book/PropNN.lean` is offered as a math REFERENCE.

Both run a concurrency pool over the props, tee each session's full stream-json trace to
`<propdir>/runs/`, and log cost to `<propdir>/cost/`. Monitor live with `monitor_tui.py`.

Per-prop artifacts under <propdir>/:
  runs/<phase>-<seq>-<sid>.jsonl    full streamed agent trace (git-ignored)
  cost/assumptions.json             assumptions-phase cost
  cost/prove/<seq>.json             one checkpoint per prove session: status snapshot + cumulative $
  cost/summary.json                 rollup: per-phase + overall

Usage:
  python3 scripts/run_faithful.py assumptions Book1/Prop18 [Book1/Prop19 …] [--concurrency N] [--model M] [--dry-run]
  python3 scripts/run_faithful.py prove       Book1/Prop18 [...] [--concurrency N] [--model M] [--max-resumes K] [--dry-run]

⚠ HUMAN-run orchestrator — it SPAWNS `claude`. Run it OUTSIDE an agent session, from `LeanEuclidPlus/`
(the agent build sandbox hard-denies spawning `claude`). Calibrate on ONE prop first for a real
per-prop $ before scaling to 30.
"""
import argparse
import json
import os
import subprocess
import signal
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed

sys.path.insert(0, os.path.dirname(__file__))
import faithful_lib as L

REPO_ROOT = os.path.dirname(L.BOOK_ROOT)          # the DNA repo root (holds .claude/ + CLAUDE.md)
REG_DIR = os.path.join(L.BOOK_ROOT, ".lake", "faithful_runs")   # live-run registry (git-ignored)
DEFAULT_TIMEOUT = 3 * 60 * 60                       # 3h per session wall (a prove session can be long)


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


# $ per token: (input, output, cache_write, cache_read). Used ONLY for the live-during-a-session
# estimate written to cost/live.json; the SAVED cost is always the CLI's exact `total_cost_usd`.
# Public Anthropic list prices; on a gateway (ANTHROPIC_BASE_URL) the live estimate may differ — it's a
# progress indicator, superseded by the exact number when the session ends.
MODEL_PRICES = {
    "opus":   (15 / 1e6, 75 / 1e6, 18.75 / 1e6, 1.5 / 1e6),
    "sonnet": (3 / 1e6, 15 / 1e6, 3.75 / 1e6, 0.3 / 1e6),
    "haiku":  (1 / 1e6, 5 / 1e6, 1.25 / 1e6, 0.1 / 1e6),
}


def _price(model, tok):
    """Estimate $ for accumulated token counts; None if the model isn't in the table."""
    m = (model or "").lower()
    for key, (pin, pout, pcw, pcr) in MODEL_PRICES.items():
        if key in m:
            return tok["in"] * pin + tok["out"] * pout + tok["cw"] * pcw + tok["cr"] * pcr
    return None


# ── low-level: run one headless claude session, tee the trace, extract cost ───────────────────────
def _extract_cost(obj, acc):
    """Fold a stream-json event into the running (session_id, cost_usd, usage, model, tok) accumulator."""
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
    # accumulate PER-TURN token usage (assistant events only — the result event's usage would double it)
    if obj.get("type") == "assistant":
        u = (obj.get("message") or {}).get("usage")
        if isinstance(u, dict):
            tok = acc.setdefault("tok", {"in": 0, "out": 0, "cw": 0, "cr": 0})
            tok["in"] += u.get("input_tokens") or 0
            tok["out"] += u.get("output_tokens") or 0
            tok["cw"] += u.get("cache_creation_input_tokens") or 0
            tok["cr"] += u.get("cache_read_input_tokens") or 0


def _live_path(transcript_path):
    """<propdir>/cost/live.json — the running-cost estimate for the session writing this transcript."""
    return os.path.join(os.path.dirname(os.path.dirname(transcript_path)), "cost", "live.json")


def _write_live(transcript_path, acc):
    """Best-effort: write the running token/$ estimate for the in-flight session (read by monitor_tui).
    Never let a live-write error disturb the session."""
    tok = acc.get("tok") or {"in": 0, "out": 0, "cw": 0, "cr": 0}
    try:
        p = _live_path(transcript_path)
        os.makedirs(os.path.dirname(p), exist_ok=True)
        tmp = p + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump({"est_usd": _price(acc.get("model"), tok), "tokens": tok,
                       "model": acc.get("model"), "updated": time.time()}, f)
        os.replace(tmp, p)
    except OSError:
        pass


def _clear_live(propdir):
    """Remove cost/live.json once the session's EXACT cost has been persisted (no double counting)."""
    try:
        os.remove(os.path.join(propdir, "cost", "live.json"))
    except OSError:
        pass


def claude_session(prompt, transcript_path, *, model=None, timeout=DEFAULT_TIMEOUT, dry_run=False):
    """Run one `claude -p` session. Tees every stream-json line to `transcript_path`. Returns a dict:
    {session_id, cost_usd, usage, ok, error}. On dry-run, prints the command and returns a stub."""
    # acceptEdits: headless has no human to grant an Edit/Write prompt. deny rules (signature JSONs,
    # git, lake) + the bash/step hooks still apply.
    cmd = ["claude", "-p", prompt, "--output-format", "stream-json", "--verbose",
           "--permission-mode", "acceptEdits"]
    if model:
        cmd += ["--model", model]

    if dry_run:
        print(f"    [dry-run] (cwd={REPO_ROOT}) {' '.join(_shquote(c) for c in cmd)}")
        print(f"    [dry-run] trace → {os.path.relpath(transcript_path, L.BOOK_ROOT)}")
        return {"session_id": None, "cost_usd": 0.0, "usage": {}, "ok": True, "error": None}

    os.makedirs(os.path.dirname(transcript_path), exist_ok=True)
    acc = {"session_id": None, "cost_usd": None, "usage": {}, "model": None,
           "tok": {"in": 0, "out": 0, "cw": 0, "cr": 0}}
    try:
        with open(transcript_path, "w", encoding="utf-8") as trace:
            # start_new_session=True → the child leads its own process group, so we can reap the WHOLE
            # tree (child + any grandchildren) with one killpg. This matters because a crashed `claude`
            # can leave a grandchild holding the stdout pipe open → EOF never arrives → the read loop
            # below would block this worker forever (the hang seen at high concurrency).
            proc = subprocess.Popen(cmd, cwd=REPO_ROOT, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, text=True, bufsize=1,
                                    start_new_session=True)

            def _killtree():
                try:
                    os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
                except (ProcessLookupError, PermissionError):
                    try:
                        proc.kill()
                    except ProcessLookupError:
                        pass

            # Hard watchdog: kill the whole tree if the session exceeds `timeout`.
            timed_out = {"hit": False}

            def _hard_kill():
                timed_out["hit"] = True
                _killtree()
            wd = threading.Timer(timeout, _hard_kill)
            wd.start()

            # Anti-hang reaper: once the direct child has EXITED, give the pipe a short grace to drain;
            # if EOF still hasn't arrived (a grandchild is holding it open), kill the group to force it.
            reading_done = threading.Event()

            def _reaper():
                while not reading_done.wait(0.5):
                    if proc.poll() is not None:            # child gone; wait briefly for a clean EOF
                        if not reading_done.wait(3.0):
                            _killtree()                    # force EOF on the read loop
                        return
            rp = threading.Thread(target=_reaper, daemon=True)
            rp.start()
            last_live = 0.0
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
                    now = time.time()                            # emit a live cost/token estimate ~every 2s
                    if now - last_live > 2.0:
                        _write_live(transcript_path, acc)
                        last_live = now
                rc = proc.wait()
            finally:
                reading_done.set()
                wd.cancel()
            if timed_out["hit"]:
                return {**acc, "ok": False, "error": f"timeout after {timeout}s"}
    except FileNotFoundError:
        return {**acc, "ok": False, "error": "`claude` CLI not found on PATH"}
    except MemoryError:
        return {**acc, "ok": False, "error": "MemoryError launching `claude` — the machine hit its "
                "memory-commit limit (vm.overcommit_memory=2 refuses the fork even with free RAM). "
                "LOWER --concurrency (try 1–2)."}
    if rc == 0:
        return {**acc, "ok": True, "error": None}
    if rc < 0:                                            # killed by a signal (rc == -signum)
        hint = (" — likely the OS killing it under memory pressure / strict overcommit; LOWER "
                "--concurrency (try 1–2)") if -rc in (11, 5, 9, 6) else ""
        return {**acc, "ok": False, "error": f"claude killed by signal {-rc}{hint}"}
    return {**acc, "ok": False, "error": f"claude exited {rc}"}


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


def _rename_with_sid(transcript, propdir, phase, seq, sid):
    """Append the real session id to the trace filename once known (keeps traces unique/traceable)."""
    newt = os.path.join(_runs_dir(propdir), f"{phase}-{seq}-{sid}.jsonl")
    try:
        os.replace(transcript, newt)
    except OSError:
        pass


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
    """Roll every cost/*.json into cost/summary.json (per-phase totals + overall)."""
    cost_dir = _cost_dir(propdir)
    summary = {"prop": os.path.relpath(propdir, L.BOOK_ROOT), "phases": {}, "total_usd": 0.0,
               "prove_checkpoints": []}
    p = os.path.join(cost_dir, "assumptions.json")
    if os.path.exists(p):
        rec = json.load(open(p, encoding="utf-8"))
        summary["phases"]["assumptions"] = rec.get("cost_usd", 0.0)
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


# ── segment: assumptions (one /faithful-assumptions session per prop) ──────────────────────────────
def run_assumptions(prop, *, model=None, dry_run=False):
    propdir = _abs_propdir(prop)
    if not os.path.isdir(propdir):
        return prop, False, f"propdir not found: {prop}"
    log = [f"[assumptions] {prop}"]
    if not dry_run:
        _clear_needs_human(propdir)

    transcript = os.path.join(_runs_dir(propdir), "assumptions-1.jsonl")
    prompt = (f"/faithful-assumptions {prop}  — run the Assumption Phase; if the STEP-A build fails "
              f"(a wlog frame break), FIX THE FRAME by adding the argument (NEVER delete a have) and "
              f"finish with --tag-only. Do NOT stop to ask.{_headless_note(prop)}")
    res = claude_session(prompt, transcript, model=model, dry_run=dry_run)
    if res.get("session_id") and not dry_run:
        _rename_with_sid(transcript, propdir, "assumptions", 1, res["session_id"])
    if not dry_run:
        _write_json(os.path.join(_cost_dir(propdir), "assumptions.json"),
                    {"phase": "assumptions", "session_id": res.get("session_id"),
                     "model": res.get("model"), "cost_usd": res.get("cost_usd"),
                     "usage": res.get("usage")})
        _clear_live(propdir)                          # exact cost saved → drop the live estimate
    log.append(f"  session: {'ok' if res['ok'] else 'FAIL — ' + str(res['error'])}"
               f"  ${res.get('cost_usd') or 0:.4f}")

    ok = res["ok"]
    if not dry_run and _needs_human(propdir):
        log.append(f"  ⚠ BLOCKED — agent wrote {prop}/NEEDS_HUMAN.md (human decision needed). "
                   f"Read it, resolve, delete it, then re-run.")
        ok = False
    elif ok and not dry_run:
        # Post-check: Main must still elaborate (the materialized `have`s didn't break the build).
        ok = _run_script(["scripts/check_step.py", prop, "--provable"], dry_run, log, "provable")
    if not dry_run:
        _rollup_summary(propdir)
    log.append(f"  → {'DONE (Main elaborates)' if ok else 'INCOMPLETE — inspect the trace / NEEDS_HUMAN.md'}"
               f"; next: /faithful-prove")
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
        # Each continuation is a FRESH agent (new context) — NOT a `--resume`. A fresh session re-reads
        # the on-disk state (certified step files + `check_step --status`/`--drive`) and picks up where
        # the last one left off. Progress lives on disk, not in any one session's context.
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
                _rename_with_sid(transcript, propdir, "prove", seq, sid)
        cumulative += res.get("cost_usd") or 0.0

        # checkpoint: cheap read-only status (no builds) + cumulative cost
        if dry_run:
            snap, all_done = {"nodes": [], "checks": {}}, False
        else:
            snap, all_done = _status_snapshot(propdir)
            _write_json(os.path.join(prove_dir, f"{seq}.json"),
                        {"seq": seq, "session_id": sid, "model": res.get("model"),
                         "this_session_usd": res.get("cost_usd"),
                         "cumulative_usd": cumulative, "status": snap})
            _clear_live(propdir)          # this session's exact cost is in the checkpoint now
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
        # progress. Stop resuming after STALL_LIMIT such sessions in a row.
        done = sum(1 for n in snap.get("nodes", []) if n.get("state") == "done")
        stall = stall + 1 if done <= prev_done else 0
        prev_done = max(prev_done, done)
        if stall >= STALL_LIMIT:
            log.append(f"  ⚠ STALLED — {stall} sessions with no newly-certified node ({done} done). "
                       f"Stopping to avoid burning tokens; inspect `--status`/the latest trace, fix, "
                       f"then re-run prove.")
            break
        if not res["ok"]:
            log.append("  (session failed; resuming)" if attempt < max_resumes else "  (out of resumes)")

    if not dry_run:
        _rollup_summary(propdir)
    verdict = "CERTIFIED (--all green)" if ok_all else "INCOMPLETE — inspect the latest trace / --status"
    log.append(f"  → {verdict}")
    return prop, ok_all, "\n".join(log)


# ── CLI ───────────────────────────────────────────────────────────────────────────────────────────
def main():
    ap = argparse.ArgumentParser(
        description="Headless batch driver for the two automatable faithful phases (assumptions, prove). "
                    "Everything else in the pipeline is manual/interactive.")
    ap.add_argument("segment", choices=["assumptions", "prove"],
                    help="assumptions = the Assumption Phase (/faithful-assumptions per prop); "
                         "prove = the resumable Phase-B loop until check_step --all passes.")
    ap.add_argument("props", nargs="+", help="prop dirs, e.g. Book1/Prop18 Book1/Prop19")
    ap.add_argument("--concurrency", type=int, default=4, help="max props in flight (default 4)")
    ap.add_argument("--model", default=None, help="override the claude model (default: session default)")
    ap.add_argument("--max-resumes", type=int, default=6, help="prove: max resume sessions per prop")
    ap.add_argument("--dry-run", action="store_true", help="print the plan; spawn nothing")
    args = ap.parse_args()

    runners = {
        "assumptions": lambda p: run_assumptions(p, model=args.model, dry_run=args.dry_run),
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
