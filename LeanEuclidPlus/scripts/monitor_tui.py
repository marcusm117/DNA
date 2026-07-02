#!/usr/bin/env python3
"""Interactive live monitor for run_faithful batches.

One screen: a GLOBAL table of every prop being worked (phase · nodes done/total · cost · status),
and — for the focused prop — its newest trace tailing live. Auto-refreshes; switch focus anytime.
It **auto-discovers** what's running from the run_faithful registry (`.lake/faithful_runs/*.json`),
so you don't re-type prop names. **Read-only and decoupled** — quitting or switching NEVER affects a
running batch.

Usage:
  python3 scripts/monitor_tui.py                       # auto-discover active run_faithful batches
  python3 scripts/monitor_tui.py Book1/Prop08 Book1/Prop14   # monitor these explicitly
  python3 scripts/monitor_tui.py --once                # print one frame and exit (non-interactive/testable)

Keys:  [0-9] focus that prop · ↑/↓ move focus · g toggle global-only · q quit
"""
import argparse
import glob
import json
import os
import shutil
import sys

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


def summarize(pd):
    """Coarse per-prop state read straight off disk (phase, nodes done/total, cost, flag)."""
    name = os.path.relpath(pd, L.BOOK_ROOT)
    cdir = os.path.join(pd, "cost")
    cost = 0.0
    for ph in ("split", "translate", "reconcile"):
        r = _load(os.path.join(cdir, ph + ".json"))
        cost += (r.get("cost_usd") or 0) if r else 0
    pv = glob.glob(os.path.join(cdir, "prove", "*.json"))
    if pv:
        r = _load(max(pv, key=lambda p: int(os.path.basename(p)[:-5]) if os.path.basename(p)[:-5].isdigit() else 0))
        cost += (r.get("cumulative_usd") or 0) if r else 0
    done = tot = 0
    try:
        rows, _ = L.status_rows(pd)
        tot = len(rows)
        done = sum(1 for _, st, _ in rows if st == "done")
    except Exception:
        pass
    has_prove = os.path.isdir(os.path.join(cdir, "prove"))
    phase = ("prove" if has_prove else
             "mapped" if os.path.exists(os.path.join(pd, "translate.json")) else
             "split" if os.path.exists(os.path.join(pd, "split.json")) else "—")
    flag = ("BLOCKED" if os.path.exists(os.path.join(pd, "NEEDS_HUMAN.md")) else
            "DONE" if (tot and done == tot) else "")
    return name, phase, done, tot, cost, flag


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


def _prop_row(i, props, focus):
    pd, live = props[i]
    name, phase, done, tot, cost, flag = summarize(pd)
    mark = ">" if i == focus else " "
    return "%s %2d  %-20s  %-7s  %3d/%-3d  $%-8.4f %s%s" % (
        mark, i, name[:20], phase, done, tot, cost, flag, ("  ●live" if live else ""))


def render_lines(props, focus, global_only, height, width):
    """Full frame as lines, WINDOWED so a big batch never buries the trace: the prop table shows a
    slice AROUND `focus` (with ▲/▼ 'N more' markers), and the focused prop's trace tail fills the rest.
    In global-only mode the table takes the whole height (still windowed/scrollable via focus)."""
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
        out.append(_prop_row(i, props, focus))
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


def build_once(props, focus, global_only):
    size = shutil.get_terminal_size((100, 40))
    return "\n".join(render_lines(props, focus, global_only, size.lines, size.columns))


def loop(scr, get_props, interval):
    import curses
    curses.curs_set(0)
    focus, global_only, numbuf = 0, False, ""
    while True:
        props = get_props()
        if focus >= len(props):
            focus = max(0, len(props) - 1)
        scr.erase()
        H, Wd = scr.getmaxyx()
        for r, ln in enumerate(render_lines(props, focus, global_only, H, Wd)):
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


def main():
    ap = argparse.ArgumentParser(description="Interactive live monitor for run_faithful batches.")
    ap.add_argument("props", nargs="*", help="prop dirs to monitor (default: auto-discover from registry)")
    ap.add_argument("--once", action="store_true", help="print one frame and exit (non-interactive)")
    ap.add_argument("--dump", action="store_true",
                    help="print the FULL trace of the first prop (all events) to stdout — pipe to less")
    ap.add_argument("--interval", type=float, default=1.5, help="refresh seconds (default 1.5)")
    args = ap.parse_args()

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
        print(build_once(get_props(), 0, False))
        return
    import curses
    curses.wrapper(lambda scr: loop(scr, get_props, args.interval))


if __name__ == "__main__":
    main()
