#!/usr/bin/env python3
"""Interactive live monitor for run_faithful batches (assumptions / prove).

One screen: a GLOBAL table of every prop being worked (phase · nodes done/total · cost · status),
and — for the focused prop — its newest trace tailing live. Auto-refreshes; switch focus anytime.
It **auto-discovers** what's running from the run_faithful registry (`.lake/faithful_runs/*.json`),
so you don't re-type prop names. **Read-only and decoupled** — quitting or switching NEVER affects a
running batch.

No-lag by design: the expensive per-prop status computation runs in a BACKGROUND thread (round-robin
over the props into a cache); the curses render only ever reads the cache, so it stays instant even
with 30+ props. The focused prop's trace tail is read live but bounded (128 KB), so it's cheap too.

Usage:
  python3 scripts/monitor_tui.py                       # auto-discover active run_faithful batches
  python3 scripts/monitor_tui.py Book1/Prop08 Book1/Prop14   # monitor these explicitly
  python3 scripts/monitor_tui.py --once                # print one frame and exit (non-interactive/testable)
  python3 scripts/monitor_tui.py --dump Book1/Prop08   # full trace of one prop, for scrollback
  python3 scripts/monitor_tui.py --selftest [N]        # benchmark refresh+render over N real props (no lag proof)

Keys:  [0-9]+Enter jump to that prop · ↑/↓ move focus · g toggle global-only · q quit
"""
import argparse
import glob
import json
import os
import re
import shutil
import sys
import threading
import time

sys.path.insert(0, os.path.dirname(__file__))
import faithful_lib as L

REG_DIR = os.path.join(L.BOOK_ROOT, ".lake", "faithful_runs")


def newest_trace(propdir):
    """The most-recently-written trace under <propdir>/runs/ (the session currently streaming)."""
    fs = glob.glob(os.path.join(propdir, "runs", "*.jsonl"))
    return max(fs, key=os.path.getmtime) if fs else None


def _abs(p):
    return p if os.path.isabs(p) else os.path.join(L.BOOK_ROOT, p)


def _alive(pid):
    try:
        os.kill(int(pid), 0)
    except ProcessLookupError:
        return False
    except (PermissionError, ValueError, TypeError):
        return True
    return True


def discover(explicit):
    """Return [(propdir_abs, live_bool)]. Explicit args win; else read the registry."""
    seen = {}
    if explicit:
        for p in explicit:
            seen[_abs(p)] = True
    else:
        for f in glob.glob(os.path.join(REG_DIR, "*.json")):
            try:
                reg = json.load(open(f))
            except (ValueError, OSError):
                continue
            live = _alive(reg.get("pid", -1))
            for p in reg.get("props", []):
                ap = _abs(p)
                seen[ap] = seen.get(ap, False) or live
    return sorted(seen.items(), key=lambda kv: kv[0])


def _load(p):
    try:
        return json.load(open(p))
    except (ValueError, OSError):
        return None


def _short(pd):
    """Display label: the trailing `BookN/PropNN` if present (works for real props under BOOK_ROOT AND
    for out-of-tree/mock props), else the plain relpath."""
    parts = pd.rstrip(os.sep).split(os.sep)
    if len(parts) >= 2 and re.fullmatch(r"Book\d+", parts[-2]):
        return parts[-2] + "/" + parts[-1]
    return os.path.relpath(pd, L.BOOK_ROOT)


def _latest_checkpoint(cdir):
    """The highest-seq cost/prove/<seq>.json record, or None."""
    pv = glob.glob(os.path.join(cdir, "prove", "*.json"))
    if not pv:
        return None
    latest = max(pv, key=lambda p: int(os.path.basename(p)[:-5]) if os.path.basename(p)[:-5].isdigit() else 0)
    return _load(latest)


def summarize(pd):
    """Coarse per-prop state read straight off disk (phase, nodes done/total, cost, flag).

    Deliberately CHEAP: progress is `#Main nodes with a subtree certificate / #Main nodes`, read from
    the manifest (one JSON) + a single Main.lean parse — NOT the full `status_rows` (which re-hashes
    every backing file and re-scans deps/integrity/orphans, up to tens of seconds on a big prop). A
    monitor wants fresh, not authoritative — the authoritative gate is `check_step --all` / `--status`.
    When there's no manifest yet (a just-started prop, or a mock batch), it falls back to the latest
    prove checkpoint's status snapshot. Staleness/whole-prop checks are intentionally omitted here."""
    name = _short(pd)
    cdir = os.path.join(pd, "cost")
    cost = 0.0
    estimated = False
    r = _load(os.path.join(cdir, "assumptions.json"))
    cost += (r.get("cost_usd") or 0) if r else 0
    ckpt = _latest_checkpoint(cdir)
    if ckpt:
        cost += ckpt.get("cumulative_usd") or 0
    live = _load(os.path.join(cdir, "live.json"))     # in-flight session's running estimate (~2s fresh)
    if live and live.get("est_usd") is not None:
        cost += live.get("est_usd") or 0
        estimated = True
    done = tot = 0
    mains = None
    try:
        mains = L.main_nodes_in_order(pd)
        tot = len(mains)
    except Exception:
        mains = None
    subtrees = L.read_manifest(pd).get("subtrees", {})
    if mains is not None and subtrees:
        done = sum(1 for nd in mains if nd.name in subtrees)
    elif ckpt:                                   # no manifest → the checkpoint snapshot is the truth
        nodes = (ckpt.get("status") or {}).get("nodes") or []
        done = sum(1 for n in nodes if n.get("state") == "done")
        tot = tot or len(nodes)
    phase = ("prove" if os.path.isdir(os.path.join(cdir, "prove")) else
             "assump" if os.path.exists(os.path.join(cdir, "assumptions.json")) else
             "mapped" if os.path.exists(os.path.join(pd, "Main.lean")) else "—")
    flag = ("BLOCKED" if os.path.exists(os.path.join(pd, "NEEDS_HUMAN.md")) else
            "DONE?" if (tot and done == tot) else "")
    return name, phase, done, tot, cost, flag, estimated


def _tool_arg(inp):
    if isinstance(inp, dict):
        for k in ("command", "file_path", "pattern", "query", "path"):
            if k in inp:
                return " ".join(str(inp[k]).split())[:120]
        return json.dumps(inp)[:120]
    return str(inp)[:120]


def plain_event(o):
    """One or more plain-text lines for a stream-json event (no ANSI — curses/plain safe)."""
    t = o.get("type")
    if t == "system":
        return ["· session %s · %s" % (str(o.get("session_id"))[:8], o.get("model"))]
    if t == "assistant":
        out = []
        for b in (o.get("message") or {}).get("content") or []:
            bt = b.get("type")
            if bt == "thinking":
                out.append("  think: " + " ".join(b.get("thinking", "").split())[:400])
            elif bt == "text" and b.get("text", "").strip():
                out.append("  say:   " + " ".join(b["text"].split())[:400])
            elif bt == "tool_use":
                out.append("  > %s  %s" % (b.get("name"), _tool_arg(b.get("input"))))
        return out
    if t == "user":
        for b in (o.get("message") or {}).get("content") or []:
            if isinstance(b, dict) and b.get("type") == "tool_result":
                c = b.get("content")
                if isinstance(c, list):
                    c = " ".join(x.get("text", "") for x in c if isinstance(x, dict))
                return ["    <- " + " ".join(str(c).split())[:120]]
        return []
    if t == "result":
        cc = o.get("total_cost_usd") or (o.get("usage") or {}).get("total_cost_usd") or 0
        return ["== done  $%.4f · %s turns" % (cc, o.get("num_turns"))]
    return []


def trace_lines(pd, tail_bytes: "int | None" = 131072):
    """Rendered event lines for the prop's newest trace. `tail_bytes` bounds the read (live TUI stays
    fast on multi-MB traces); pass tail_bytes=None to render the WHOLE trace (used by --dump)."""
    tr = newest_trace(pd)
    if not tr:
        return None, []
    lines = []
    try:
        with open(tr, "rb") as f:
            if tail_bytes:
                f.seek(0, 2)
                size = f.tell()
                f.seek(max(0, size - tail_bytes))
                if size > tail_bytes:
                    f.readline()                      # drop the partial first line after seeking
                data = f.read()
            else:
                data = f.read()
        for raw in data.decode("utf-8", "replace").splitlines():
            raw = raw.strip()
            if raw.startswith("{"):
                try:
                    lines.extend(plain_event(json.loads(raw)))
                except ValueError:
                    pass
    except OSError:
        pass
    return tr, lines


# ── background status cache (the anti-lag core) ──────────────────────────────────────────────────
class StatusCache:
    """Refreshes each prop's `summarize()` round-robin in a daemon thread. The render loop only ever
    reads the cache (instant), so a big batch never lags the UI. A prop not yet computed reads as None
    (rendered as '…') until its first pass lands."""

    def __init__(self, get_props, per_prop_pause=0.02, cycle_pause=0.5):
        self.get_props = get_props
        self.per_prop_pause = per_prop_pause      # tiny yield between props (keeps one CPU from pegging)
        self.cycle_pause = cycle_pause            # rest at the end of a full sweep
        self._cache = {}
        self._lock = threading.Lock()
        self._stop = threading.Event()
        self._thread = threading.Thread(target=self._loop, daemon=True)

    def start(self):
        self._thread.start()
        return self

    def stop(self):
        self._stop.set()

    def get(self, pd):
        with self._lock:
            return self._cache.get(pd)

    def _loop(self):
        while not self._stop.is_set():
            props = self.get_props()
            if not props:
                self._stop.wait(1.0)
                continue
            for pd, _ in props:
                if self._stop.is_set():
                    break
                try:
                    s = summarize(pd)
                except Exception:
                    s = (os.path.relpath(pd, L.BOOK_ROOT), "?", 0, 0, 0.0, "")
                with self._lock:
                    self._cache[pd] = s
                self._stop.wait(self.per_prop_pause)
            self._stop.wait(self.cycle_pause)


def _prop_row(i, props, focus, getter):
    pd, live = props[i]
    s = getter(pd)
    mark = ">" if i == focus else " "
    if s is None:
        return "%s %2d  %-20s  %s" % (mark, i, os.path.relpath(pd, L.BOOK_ROOT)[:20], "…")
    name, phase, done, tot, cost, flag, estimated = s
    money = ("~$%-7.4f" % cost) if estimated else (" $%-7.4f" % cost)   # ~ = live estimate, not final
    return "%s %2d  %-20s  %-7s  %3d/%-3d %s %s%s" % (
        mark, i, name[:20], phase, done, tot, money, flag, ("  ●live" if live else ""))


def render_lines(props, focus, global_only, height, width, getter):
    """Full frame as lines, WINDOWED so a big batch never buries the trace: the prop table shows a
    slice AROUND `focus` (with ▲/▼ 'N more' markers), and the focused prop's trace tail fills the rest.
    `getter(pd)` returns a cached summary tuple or None. In global-only mode the table takes the whole
    height (still windowed/scrollable via focus)."""
    out = ["run_faithful monitor   ·   type #+Enter to jump   ↑/↓ move   g global   q quit",
           "  #  prop                  phase    nodes    cost       status"]
    if not props:
        out.append("  (no active batch — start run_faithful, or pass prop dirs as args)")
        return [ln[:width - 1] for ln in out]

    # rows to show: whole screen in global-only, ~half otherwise (leave the rest for the trace)
    cap = (height - len(out) - 2) if global_only else max(3, height // 2 - 1)
    cap = max(1, min(cap, len(props)))
    start = max(0, min(focus - cap // 2, len(props) - cap)) if len(props) > cap else 0
    if start > 0:
        out.append("   ▲ %d more above" % start)
    for i in range(start, min(start + cap, len(props))):
        out.append(_prop_row(i, props, focus, getter))
    below = len(props) - (start + cap)
    if below > 0:
        out.append("   ▼ %d more below" % below)

    if not global_only:
        pd = props[focus][0]
        tr, tl = trace_lines(pd)
        out.append("── TRACE %s ──" % (os.path.relpath(tr, L.BOOK_ROOT) if tr else "(none yet)"))
        avail = max(0, height - len(out))
        out.extend(tl[-avail:] if avail else [])
    return [ln[:width - 1] for ln in out]


def build_once(props, focus, global_only, getter):
    size = shutil.get_terminal_size((100, 40))
    return "\n".join(render_lines(props, focus, global_only, size.lines, size.columns, getter))


def loop(scr, get_props, cache, interval):
    import curses
    curses.curs_set(0)
    focus, global_only, numbuf = 0, False, ""
    while True:
        props = get_props()
        if focus >= len(props):
            focus = max(0, len(props) - 1)
        scr.erase()
        H, Wd = scr.getmaxyx()
        for r, ln in enumerate(render_lines(props, focus, global_only, H, Wd, cache.get)):
            if r >= H:
                break
            try:
                scr.addnstr(r, 0, ln, Wd - 1)
            except curses.error:
                pass
        if numbuf:
            try:
                scr.addnstr(H - 1, 0, "jump to #: %s   (Enter = go · Esc = cancel)" % numbuf, Wd - 1)
            except curses.error:
                pass
        scr.refresh()
        scr.timeout(int(interval * 1000))
        ch = scr.getch()
        if ch == -1:
            continue
        if ch == ord("q"):
            break
        elif ch == 27:                                    # Esc cancels a pending jump
            numbuf = ""
        elif ch == ord("g"):
            global_only = not global_only
        elif ch == curses.KEY_UP:
            focus, numbuf = max(0, focus - 1), ""
        elif ch == curses.KEY_DOWN and props:
            focus, numbuf = min(len(props) - 1, focus + 1), ""
        elif ord("0") <= ch <= ord("9"):
            numbuf += chr(ch)                             # accumulate a multi-digit index
        elif ch in (10, 13, curses.KEY_ENTER):
            if numbuf.isdigit() and int(numbuf) < len(props):
                focus = int(numbuf)
            numbuf = ""
        elif ch in (curses.KEY_BACKSPACE, 127, 8):
            numbuf = numbuf[:-1]
        else:
            numbuf = ""


def _all_real_props():
    """Every Book*/Prop* dir that has a Main.lean — for --selftest."""
    out = []
    for book in sorted(glob.glob(os.path.join(L.BOOK_ROOT, "Book*"))):
        for pd in sorted(glob.glob(os.path.join(book, "Prop*"))):
            if os.path.isfile(os.path.join(pd, "Main.lean")):
                out.append(pd)
    return out


def selftest(n):
    """Benchmark the anti-lag design over N real props: time a full status sweep (the background
    thread's work) and — the number that matters — the CACHED render latency the UI actually sees."""
    props_dirs = _all_real_props()
    if n:
        props_dirs = props_dirs[:n]
    if not props_dirs:
        print("selftest: no props with Main.lean found")
        return 1
    props = [(pd, True) for pd in props_dirs]
    print(f"selftest over {len(props)} real props")

    # 1) full status sweep (what the background thread does once per cycle)
    t0 = time.perf_counter()
    cache = {}
    per = []
    for pd, _ in props:
        s0 = time.perf_counter()
        cache[pd] = summarize(pd)
        per.append((time.perf_counter() - s0) * 1000)
    sweep_ms = (time.perf_counter() - t0) * 1000
    per.sort()
    print(f"  status sweep (all props): {sweep_ms:8.1f} ms total  ·  "
          f"per-prop avg {sweep_ms/len(props):5.1f} · max {per[-1]:5.1f} ms")

    # 2) CACHED render latency — this is what the curses loop pays every frame. Must be tiny.
    size = shutil.get_terminal_size((120, 45))
    worst = 0.0
    for focus in range(0, len(props), max(1, len(props) // 20)):
        r0 = time.perf_counter()
        render_lines(props, focus, False, size.lines, size.columns, cache.get)
        worst = max(worst, (time.perf_counter() - r0) * 1000)
    print(f"  cached render latency (worst of sampled focuses): {worst:6.2f} ms")

    # 3) large-trace tail: render latency should not grow with trace size (bounded tail read)
    big = os.path.join("/tmp", "faithful_selftest_big.jsonl")
    ev = json.dumps({"type": "assistant", "message": {"content": [
        {"type": "thinking", "thinking": "x " * 200},
        {"type": "tool_use", "name": "Bash", "input": {"command": "echo " + "y" * 200}}]}}) + "\n"
    with open(big, "w") as f:
        for _ in range(20000):                        # ~ multi-MB trace
            f.write(ev)
    mb = os.path.getsize(big) / 1e6
    # exercise the exact bounded-tail logic trace_lines uses (128 KB window), timed:
    t0 = time.perf_counter()
    with open(big, "rb") as f:
        f.seek(0, 2)
        size_b = f.tell()
        f.seek(max(0, size_b - 131072))
        f.readline()
        data = f.read()
    n_lines = len(data.decode("utf-8", "replace").splitlines())
    tail_ms = (time.perf_counter() - t0) * 1000
    print(f"  large-trace tail read ({mb:.1f} MB file → {n_lines} tail lines): {tail_ms:6.2f} ms")
    os.remove(big)

    ok = worst < 50.0
    print(f"  VERDICT: {'PASS' if ok else 'FAIL'} — cached render {'<' if ok else '≥'} 50 ms "
          f"(the UI never blocks on status; sweeps happen off-thread).")
    return 0 if ok else 1


def main():
    ap = argparse.ArgumentParser(description="Interactive live monitor for run_faithful batches.")
    ap.add_argument("props", nargs="*", help="prop dirs to monitor (default: auto-discover from registry)")
    ap.add_argument("--once", action="store_true", help="print one frame and exit (non-interactive)")
    ap.add_argument("--dump", action="store_true",
                    help="print the FULL trace of the first prop (all events) to stdout — pipe to less")
    ap.add_argument("--selftest", nargs="?", const=0, type=int, metavar="N",
                    help="benchmark refresh+render over N real props (default: all) and exit")
    ap.add_argument("--interval", type=float, default=1.0, help="refresh seconds (default 1.0)")
    args = ap.parse_args()

    if args.selftest is not None:
        sys.exit(selftest(args.selftest))

    def get_props():
        return discover(args.props)

    if args.dump:                                 # whole thought-chain for one prop, for scrollback
        props = get_props()
        if not props:
            print("no prop to dump (pass a prop dir, e.g. monitor_tui.py Book1/Prop08 --dump)")
            return
        pd = props[0][0]
        tr, tl = trace_lines(pd, tail_bytes=None)     # None = render the WHOLE trace
        print("TRACE %s\n" % (os.path.relpath(tr, L.BOOK_ROOT) if tr else "(none yet)"))
        print("\n".join(tl))
        return

    if args.once or not sys.stdin.isatty():
        # synchronous single frame (no background thread needed)
        props = get_props()
        cache = {pd: summarize(pd) for pd, _ in props}
        print(build_once(props, 0, False, cache.get))
        return

    cache = StatusCache(get_props).start()
    try:
        import curses
        curses.wrapper(lambda scr: loop(scr, get_props, cache, args.interval))
    finally:
        cache.stop()


if __name__ == "__main__":
    main()
