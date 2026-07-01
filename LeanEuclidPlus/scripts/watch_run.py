#!/usr/bin/env python3
"""Live viewer for run_faithful.py sessions — turn the raw stream-json trace into a readable feed of
thinking / tool calls / output, plus a cost summary.

Usage (run in YOUR terminal, alongside a running `run_faithful.py`):
  python3 scripts/watch_run.py Book1/Prop08                 # cost summary + snapshot of the newest trace
  python3 scripts/watch_run.py Book1/Prop08 --follow        # …and live-tail the active session
  python3 scripts/watch_run.py Book1/Prop08/runs/split-1.jsonl --follow   # tail one specific trace
  python3 scripts/watch_run.py Book1/Prop08 --cost          # cost only, no trace
  python3 scripts/watch_run.py <arg> --full                 # don't truncate long thinking/tool text

A prop arg resolves the newest `<propdir>/runs/*.jsonl` (the session currently streaming). `--follow`
survives the mid-run rename `split-1.jsonl → split-1-<sid>.jsonl` (it follows the file by inode).
"""
import argparse
import glob
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(__file__))
import faithful_lib as L

# light ANSI (only when stdout is a tty)
_TTY = sys.stdout.isatty()
def _c(code, s):
    return f"\033[{code}m{s}\033[0m" if _TTY else s
DIM, CYAN, GREEN, YELLOW, BOLD = "2", "36", "32", "33", "1"


def _trunc(s, n, full):
    s = " ".join(str(s).split())
    return s if full or len(s) <= n else s[:n] + " …"


def _tool_brief(inp, full):
    if not isinstance(inp, dict):
        return _trunc(inp, 160, full)
    for k in ("command", "file_path", "pattern", "query", "path"):
        if k in inp:
            return _trunc(inp[k], 200, full)
    return _trunc(json.dumps(inp, ensure_ascii=False), 160, full)


def pretty_event(obj, full=False):
    """One formatted line-group for a stream-json event, or None to skip."""
    if not isinstance(obj, dict):
        return None
    t = obj.get("type")
    if t == "system":
        return _c(DIM, f"── session {obj.get('session_id','?')[:8]} · model {obj.get('model','?')}")
    if t == "assistant":
        out = []
        for b in (obj.get("message") or {}).get("content") or []:
            if not isinstance(b, dict):
                continue
            bt = b.get("type")
            if bt == "thinking":
                out.append(_c(DIM, "💭 " + _trunc(b.get("thinking", ""), 600, full)))
            elif bt == "text" and b.get("text", "").strip():
                out.append("🗣  " + _trunc(b.get("text", ""), 800, full))
            elif bt == "tool_use":
                out.append(_c(CYAN, f"▶ {b.get('name','?')}") + "  " +
                           _tool_brief(b.get("input"), full))
        return "\n".join(out) if out else None
    if t == "user":
        for b in (obj.get("message") or {}).get("content") or []:
            if isinstance(b, dict) and b.get("type") == "tool_result":
                c = b.get("content")
                if isinstance(c, list):
                    c = " ".join(x.get("text", "") for x in c if isinstance(x, dict))
                return _c(DIM, "  ↳ " + _trunc(c, 200, full))
        return None
    if t == "result":
        cost = obj.get("total_cost_usd") or (obj.get("usage") or {}).get("total_cost_usd")
        dur = (obj.get("duration_ms") or 0) / 1000
        return _c(GREEN, _c(BOLD, f"═ done") +
                  f"  ${cost or 0:.4f} · {dur:.0f}s · {obj.get('num_turns','?')} turns"
                  f" · {obj.get('subtype','')}")
    return None


def print_cost(propdir):
    cost_dir = os.path.join(propdir, "cost")
    if not os.path.isdir(cost_dir):
        print(_c(DIM, "  (no cost/ yet)"))
        return
    print(_c(BOLD, "COST"))
    for phase in ("split", "translate"):
        p = os.path.join(cost_dir, f"{phase}.json")
        if os.path.exists(p):
            r = json.load(open(p))
            print(f"  {phase:9s} ${r.get('cost_usd') or 0:.4f}  [{r.get('model','?')}]  "
                  f"{(r.get('usage') or {}).get('output_tokens','?')} out-tok")
    prove_dir = os.path.join(cost_dir, "prove")
    if os.path.isdir(prove_dir):
        cps = sorted((f for f in os.listdir(prove_dir) if f.endswith(".json")), key=L.natural_key)
        for f in cps:
            r = json.load(open(os.path.join(prove_dir, f)))
            done = sum(1 for n in r.get("status", {}).get("nodes", []) if n.get("state") == "done")
            tot = len(r.get("status", {}).get("nodes", []))
            print(f"  prove #{r.get('seq','?')}  ${r.get('this_session_usd') or 0:.4f}  "
                  f"(cum ${r.get('cumulative_usd') or 0:.4f})  nodes {done}/{tot} done")
    s = os.path.join(cost_dir, "summary.json")
    if os.path.exists(s):
        print(_c(BOLD, f"  TOTAL ${json.load(open(s)).get('total_usd') or 0:.4f}"))


def newest_trace(propdir):
    files = glob.glob(os.path.join(propdir, "runs", "*.jsonl"))
    return max(files, key=os.path.getmtime) if files else None


def stream(path, follow, full):
    """Pretty-print a trace; with follow, keep tailing (survives rename — we hold the fd)."""
    while follow and not os.path.exists(path):
        print(_c(DIM, f"  waiting for {os.path.relpath(path)} …"), end="\r")
        time.sleep(1)
    with open(path, encoding="utf-8") as f:
        while True:
            line = f.readline()
            if line:
                line = line.strip()
                if line.startswith("{"):
                    try:
                        out = pretty_event(json.loads(line), full)
                        if out:
                            print(out)
                    except ValueError:
                        pass
            elif follow:
                time.sleep(0.4)
            else:
                break


def main():
    ap = argparse.ArgumentParser(description="Readable live viewer for run_faithful traces.")
    ap.add_argument("path", help="a propdir (Book1/Prop08) or a specific runs/*.jsonl")
    ap.add_argument("--follow", "-f", action="store_true", help="live-tail the (newest) trace")
    ap.add_argument("--cost", action="store_true", help="print the cost summary only")
    ap.add_argument("--full", action="store_true", help="don't truncate thinking/tool text")
    args = ap.parse_args()

    raw = args.path
    abspath = raw if os.path.isabs(raw) else os.path.join(L.BOOK_ROOT, raw)

    if raw.endswith(".jsonl"):
        stream(abspath, args.follow, args.full)
        return

    # propdir mode
    propdir = abspath
    if not os.path.isdir(propdir):
        sys.exit(f"not a propdir or trace: {raw}")
    print_cost(propdir)
    if args.cost:
        return
    trace = newest_trace(propdir)
    if not trace:
        if args.follow:
            print(_c(DIM, "  no trace yet; waiting…"))
            # wait for the first trace to appear, then follow it
            while not newest_trace(propdir):
                time.sleep(1)
            trace = newest_trace(propdir)
        else:
            print(_c(DIM, "  (no runs/*.jsonl yet)"))
            return
    assert trace is not None
    print(_c(BOLD, f"\nTRACE {os.path.relpath(trace, L.BOOK_ROOT)}"))
    stream(trace, args.follow, args.full)


if __name__ == "__main__":
    main()
