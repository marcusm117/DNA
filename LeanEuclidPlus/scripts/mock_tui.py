#!/usr/bin/env python3
"""mock_tui.py — drive `monitor_tui.py` with a FAKE run_faithful batch (no `claude`, no cost).

Fabricates a self-contained sandbox of mock props under `.lake/faithful_mock/` (git-ignored) and writes
the SAME on-disk artifacts a real `run_faithful.py` batch produces — a registry entry (so the TUI
auto-discovers it), per-prop `cost/prove/<seq>.json` checkpoints, and streaming `runs/*.jsonl` traces —
then advances them on a timer. Nothing real is touched: no `Book*/Prop*` dirs, no `.lake/faithful-certified`.

Test it in TWO terminals:
  term 1:  python3 scripts/mock_tui.py --props 35            # start the fake batch (Ctrl-C to stop)
  term 2:  python3 scripts/monitor_tui.py                    # auto-discovers it; watch it move

Or one-shot:
  python3 scripts/mock_tui.py --snapshot --props 40          # lay down one static frame, leave files
  python3 scripts/monitor_tui.py --once                      # render it
  python3 scripts/mock_tui.py --clean                        # remove the sandbox + registry

Flags:
  --props N     number of mock props (default 30)
  --tick S      seconds between updates (default 1.0)
  --duration S  stop after S seconds (default 0 = run until Ctrl-C)
  --seed K      RNG seed for reproducible progress/cost (default 0)
  --snapshot    write ONE partial frame and exit, leaving the sandbox in place (no live loop)
  --clean       delete the sandbox + this tool's registry files and exit
"""
import argparse
import glob
import json
import os
import random
import shutil
import sys
import time

sys.path.insert(0, os.path.dirname(__file__))
import faithful_lib as L

REG_DIR = os.path.join(L.BOOK_ROOT, ".lake", "faithful_runs")
MOCK_ROOT = os.path.join(L.BOOK_ROOT, ".lake", "faithful_mock")
MOCK_BOOK = "Book9"                       # a book number that does NOT exist for real → obviously mock

TOOLS = [("Bash", "python3 scripts/check_step.py {p} --subtree step{n}"),
         ("Read", "{p}/step{n}.lean"),
         ("Bash", "python3 scripts/scaffold_step.py {p} step{n}"),
         ("Edit", "{p}/step{n}.lean")]


def _rel(pd):
    return os.path.relpath(pd, L.BOOK_ROOT)


def _reg_path():
    return os.path.join(REG_DIR, f"mock-{os.getpid()}.json")


def _write_registry(props):
    os.makedirs(REG_DIR, exist_ok=True)
    with open(_reg_path(), "w", encoding="utf-8") as f:
        json.dump({"pid": os.getpid(), "segment": "prove", "props": [_rel(p) for p in props],
                   "started": time.time()}, f)


def _clear_registry():
    try:
        os.remove(_reg_path())
    except OSError:
        pass


def _write_checkpoint(pd, seq, done, tot, cumulative, this_usd):
    nodes = [{"name": f"step{i}", "state": ("done" if i <= done else "todo"),
              "detail": ("certified" if i <= done else "todo")} for i in range(1, tot + 1)]
    rec = {"seq": seq, "session_id": f"mock{os.getpid():05d}", "model": "claude-mock",
           "this_session_usd": round(this_usd, 4), "cumulative_usd": round(cumulative, 4),
           "status": {"nodes": nodes, "checks": {}}}
    p = os.path.join(pd, "cost", "prove", f"{seq}.json")
    os.makedirs(os.path.dirname(p), exist_ok=True)
    tmp = p + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(rec, f, indent=2)
    os.replace(tmp, p)


def _append_trace(pd, sid, events):
    p = os.path.join(pd, "runs", f"prove-1-{sid}.jsonl")
    os.makedirs(os.path.dirname(p), exist_ok=True)
    with open(p, "a", encoding="utf-8") as f:
        for e in events:
            f.write(json.dumps(e) + "\n")


def _trace_burst(rel, node, rng):
    """A few stream-json events mimicking one node's work (thinking → tool_use → tool_result)."""
    name, tmpl = rng.choice(TOOLS)
    inp = ({"command": tmpl.format(p=rel, n=node)} if name == "Bash"
           else {"file_path": tmpl.format(p=rel, n=node)})
    return [
        {"type": "assistant", "message": {"content": [
            {"type": "thinking", "thinking": f"Working step{node} of {rel}: decompose and certify."},
            {"type": "tool_use", "name": name, "input": inp}]}},
        {"type": "user", "message": {"content": [
            {"type": "tool_result", "content": f"step{node}: SF ok · SP ok · P ok" if rng.random() > 0.3
             else f"step{node}: building (≤30s cap)…"}]}},
    ]


class MockProp:
    """One mock prop slot. It advances toward `tot` certified nodes, sometimes blocks, and when it
    finishes/blocks it lingers a few ticks then RECYCLES into a fresh prop — so a running batch never
    goes quiet until you stop it."""

    def __init__(self, idx, rng):
        self.pd = os.path.join(MOCK_ROOT, MOCK_BOOK, f"Prop{idx:02d}")
        self.rel = _rel(self.pd)
        self.rng = rng
        self.cum = 0.0                                   # $ accrues across the slot's lifetime
        self.gen = 0                                     # how many times this slot has recycled
        self._new_run(initial=rng.random() < 0.15)

    def _new_run(self, initial=False):
        self.gen += 1
        self.sid = f"mock{os.path.basename(self.pd)[4:]}g{self.gen}"
        self.tot = self.rng.randint(5, 24)
        self.done = self.rng.randint(0, self.tot // 2) if initial else 0
        self.seq = 0
        self.speed = self.rng.choice([1, 1, 1, 2, 3])    # nodes certified per tick (varied pace)
        self.rate = self.rng.uniform(0.05, 0.35)         # $ per certified node
        self.blocked = False
        self.cooldown = 0                                # ticks to linger on a DONE/BLOCKED state
        # ~1-in-9 runs hit a NEEDS_HUMAN block partway
        self.block_at = (self.rng.randint(2, self.tot - 1)
                         if self.rng.random() < 0.11 and self.tot > 3 else None)
        self.emit()

    def _needs_human(self, on):
        p = os.path.join(self.pd, "NEEDS_HUMAN.md")
        if on:
            os.makedirs(self.pd, exist_ok=True)
            with open(p, "w", encoding="utf-8") as f:
                f.write("MOCK block: a modeling choice needs a human decision.\n")
        else:
            try:
                os.remove(p)
            except OSError:
                pass

    def emit(self):
        """Write the current checkpoint + a trace burst."""
        self.seq += 1
        if self.seq == 1:                                # open the session trace with a system event
            _append_trace(self.pd, self.sid, [{"type": "system", "session_id": self.sid,
                                               "model": "claude-mock"}])
        for n in range(max(1, self.done - self.speed + 1), self.done + 1):
            _append_trace(self.pd, self.sid, _trace_burst(self.rel, n, self.rng))
        _write_checkpoint(self.pd, self.seq, self.done, self.tot, self.cum,
                          this_usd=self.cum / max(1, self.seq))

    def recycle(self):
        """Wipe this slot's artifacts and start a brand-new run (keeps the batch always-moving)."""
        self._needs_human(False)
        for sub in ("runs", os.path.join("cost", "prove")):
            shutil.rmtree(os.path.join(self.pd, sub), ignore_errors=True)
        self._new_run()

    def tick(self):
        if self.blocked or self.done >= self.tot:        # finished/blocked → linger, then recycle
            self.cooldown -= 1
            if self.cooldown <= 0:
                self.recycle()
            return
        if self.block_at is not None and self.done >= self.block_at:
            self.blocked = True
            self._needs_human(True)
            _append_trace(self.pd, self.sid, [{"type": "assistant", "message": {"content": [
                {"type": "text", "text": "Hit a genuine blocker — writing NEEDS_HUMAN.md and stopping."}]}}])
            self.cooldown = self.rng.randint(3, 7)
            return
        step = min(self.speed, self.tot - self.done)
        self.done += step
        self.cum += step * self.rate
        self.emit()
        if self.done >= self.tot:
            _append_trace(self.pd, self.sid, [{"type": "result", "total_cost_usd": round(self.cum, 4),
                                               "num_turns": self.seq * 4}])
            self.cooldown = self.rng.randint(3, 7)


def clean():
    import shutil
    if os.path.isdir(MOCK_ROOT):
        shutil.rmtree(MOCK_ROOT)
        print(f"removed {os.path.relpath(MOCK_ROOT, L.BOOK_ROOT)}")
    for f in glob.glob(os.path.join(REG_DIR, "mock-*.json")):
        os.remove(f)
        print(f"removed {os.path.relpath(f, L.BOOK_ROOT)}")
    print("clean.")


def main():
    ap = argparse.ArgumentParser(description="Drive monitor_tui.py with a fake run_faithful batch.")
    ap.add_argument("--props", type=int, default=30, help="number of mock props (default 30)")
    ap.add_argument("--tick", type=float, default=1.0, help="seconds between updates (default 1.0)")
    ap.add_argument("--duration", type=float, default=0.0, help="stop after S seconds (0 = until Ctrl-C)")
    ap.add_argument("--seed", type=int, default=0, help="RNG seed (default 0)")
    ap.add_argument("--snapshot", action="store_true", help="write ONE partial frame and exit (keep files)")
    ap.add_argument("--clean", action="store_true", help="delete the sandbox + registry and exit")
    args = ap.parse_args()

    if args.clean:
        clean()
        return

    props = [MockProp(i, random.Random(args.seed * 1000 + i)) for i in range(1, args.props + 1)]
    _write_registry([p.pd for p in props])         # each prop already emitted its first frame in __init__
    print(f"mock batch: {len(props)} props under {os.path.relpath(MOCK_ROOT, L.BOOK_ROOT)}  "
          f"(registry {os.path.basename(_reg_path())})")

    if args.snapshot:
        print("snapshot written. View:  python3 scripts/monitor_tui.py --once")
        print("(registry pid is now dead → props show as not-live; that's expected for a snapshot.)")
        print("Clean up with:  python3 scripts/mock_tui.py --clean")
        return

    print("Watch it live in another terminal:  python3 scripts/monitor_tui.py")
    print("This runs FOREVER (finished props recycle into fresh ones) — press Ctrl-C to stop.")
    t0 = time.time()
    try:
        while True:
            time.sleep(args.tick)
            for p in props:
                p.tick()
            n_done = sum(1 for p in props if p.done >= p.tot and not p.blocked)
            n_block = sum(1 for p in props if p.blocked)
            total = sum(p.cum for p in props)
            print(f"  tick +{time.time()-t0:5.0f}s  ·  {len(props)} props churning · "
                  f"{n_done} done · {n_block} blocked · ${total:8.2f}   (Ctrl-C to stop)",
                  end="\r", flush=True)
            if args.duration and time.time() - t0 >= args.duration:
                print("\nreached --duration; stopping.")
                break
    except KeyboardInterrupt:
        print("\ninterrupted.")
    finally:
        _clear_registry()
        print(f"\nregistry cleared. Sandbox left at {os.path.relpath(MOCK_ROOT, L.BOOK_ROOT)} "
              f"— remove with `python3 scripts/mock_tui.py --clean`.")


if __name__ == "__main__":
    main()
