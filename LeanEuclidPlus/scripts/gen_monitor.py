#!/usr/bin/env python3
"""Generate `scripts/monitor.ipynb` — a Jupyter dashboard for run_faithful runs.

Set BOOK/PROP in the first code cell, Run All, and re-run to refresh: it shows the per-phase cost,
a cost-over-time plot across prove checkpoints, and the newest session's trace rendered as markdown
(thinking / tool calls / output). Built by a generator so the .ipynb JSON is always valid.

Run once: python3 scripts/gen_monitor.py   →   writes scripts/monitor.ipynb
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(__file__))
import faithful_lib as L

INTRO = ("# Faithful-run monitor\n\n"
         "Set **BOOK / PROP** in the next cell, then **Run All**. Re-run any cell to refresh while a "
         "`run_faithful.py` job is going. Shows cost per phase, cumulative cost over prove sessions, "
         "and the newest trace (thinking / tools / output).")

SETUP = f'''import os, json, glob
import matplotlib.pyplot as plt
from IPython.display import Markdown, display

# ==== set these, then Run All; re-run to refresh ====
BOOK, PROP = 1, 14

ROOT = r"{L.BOOK_ROOT}"
PROPDIR = os.path.join(ROOT, "Book%d" % BOOK, "Prop%02d" % PROP)
print(PROPDIR, "\\n(exists:", os.path.isdir(PROPDIR), ")")'''

COST = '''def _load(p):
    return json.load(open(p)) if os.path.exists(p) else None

cost = os.path.join(PROPDIR, "cost")
for ph in ("split", "translate"):
    r = _load(os.path.join(cost, ph + ".json"))
    if r:
        print("%-9s $%.4f  [%s]" % (ph, r.get("cost_usd") or 0, r.get("model", "?")))

prove = sorted(glob.glob(os.path.join(cost, "prove", "*.json")),
               key=lambda p: int(os.path.basename(p)[:-5]) if os.path.basename(p)[:-5].isdigit() else 0)
recs = [_load(p) for p in prove]
for r in recs:
    nodes = r.get("status", {}).get("nodes", [])
    done = sum(1 for n in nodes if n.get("state") == "done")
    print("prove #%s  $%.4f  cum $%.4f  %d/%d nodes done"
          % (r.get("seq"), r.get("this_session_usd") or 0, r.get("cumulative_usd") or 0, done, len(nodes)))

summ = _load(os.path.join(cost, "summary.json"))
if summ:
    print("TOTAL  $%.4f" % (summ.get("total_usd") or 0))

if recs:
    xs = [r.get("seq") for r in recs]
    ys = [r.get("cumulative_usd") or 0 for r in recs]
    plt.figure(figsize=(6, 3))
    plt.plot(xs, ys, marker="o")
    plt.xlabel("prove session"); plt.ylabel("cumulative $")
    plt.title("Book%d/Prop%02d prove cost over time" % (BOOK, PROP))
    plt.grid(True); plt.show()'''

TRACE = '''def _newest_trace(propdir):
    fs = glob.glob(os.path.join(propdir, "runs", "*.jsonl"))
    return max(fs, key=os.path.getmtime) if fs else None

def render_trace(path):
    md = ["### trace `%s`" % os.path.basename(path)]
    for line in open(path):
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            o = json.loads(line)
        except ValueError:
            continue
        t = o.get("type")
        if t == "system":
            md.append("_session %s \\u00b7 model %s_" % (str(o.get("session_id"))[:8], o.get("model")))
        elif t == "assistant":
            for b in (o.get("message") or {}).get("content") or []:
                bt = b.get("type")
                if bt == "thinking":
                    md.append("> \\U0001f4ad " + " ".join(b.get("thinking", "").split()))
                elif bt == "text" and b.get("text", "").strip():
                    md.append(b.get("text"))
                elif bt == "tool_use":
                    md.append("**\\u25b6 %s** `%s`" % (b.get("name"), json.dumps(b.get("input"))[:220]))
        elif t == "result":
            c = o.get("total_cost_usd") or (o.get("usage") or {}).get("total_cost_usd") or 0
            md.append("**done** \\u2014 $%.4f \\u00b7 %s turns" % (c, o.get("num_turns")))
    display(Markdown(("\\n\\n").join(md)))

tr = _newest_trace(PROPDIR)
print(tr)
if tr:
    render_trace(tr)'''


def code(src):
    return {"cell_type": "code", "metadata": {}, "execution_count": None, "outputs": [], "source": src}


def main():
    nb = {
        "cells": [
            {"cell_type": "markdown", "metadata": {}, "source": INTRO},
            code(SETUP), code(COST), code(TRACE),
        ],
        "metadata": {"language_info": {"name": "python"},
                     "kernelspec": {"name": "python3", "display_name": "Python 3"}},
        "nbformat": 4, "nbformat_minor": 5,
    }
    out = os.path.join(os.path.dirname(__file__), "monitor.ipynb")
    with open(out, "w", encoding="utf-8") as f:
        json.dump(nb, f, indent=1)
        f.write("\n")
    print("wrote", os.path.relpath(out, L.BOOK_ROOT))


if __name__ == "__main__":
    main()
