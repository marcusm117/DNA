#!/usr/bin/env python3
"""
proof_map.py  --  render a LeanEuclidPlus proposition as a multi-level HTML map.

Design principles:
  • Lines are NEVER wrapped (white-space: pre) — one source line = one screen line.
  • Cards expand to fit their widest line (width: max-content).  No card scrollbars.
  • The whole page is one big canvas; scroll the browser to navigate.
  • Two global sliders in a sticky toolbar:
      Font size  (9–20 px)  — scales text, making every card wider/taller.
      Row height (1.0–3.0x) — controls vertical spacing inside cards.
  • Assumptions folded by default: [N hyps ▸] badge, click to expand.
  • Bezier connectors redraw automatically after any slider change or toggle.

USAGE (run from LeanEuclidPlus/ or repo root)
  python3 diagrams/scripts/proof_map.py --prop Book2/Prop02
  python3 diagrams/scripts/proof_map.py --prop Book2/Prop02 -o out.html
"""

import argparse, os, re, sys, html as htmllib, subprocess

# ── source parsing ────────────────────────────────────────────────────────────

def strip_block_comments(text):
    return re.sub(r"/-.*?-/", "", text, flags=re.DOTALL)

def strip_line_comment(line):
    for i in range(len(line) - 1):
        if line[i] == "-" and line[i+1] == "-":
            return line[:i]
    return line

RE_SENTENCE    = re.compile(r'euclid_\w*sentence\s+"([^"]*)"')
RE_CLAIM       = re.compile(r'\((\w+)\s*:')
RE_HAVE        = re.compile(r'^\s*have\s+(\w+)\s*(?::=|:)')
RE_THEOREM     = re.compile(r'^(?:theorem|lemma)\s+(\w+)')

def classify_line(line):
    s = line.strip()
    m = RE_SENTENCE.search(s)
    if m:
        cm = RE_CLAIM.search(s)
        return ("sentence", cm.group(1) if cm else None, m.group(1))
    m = RE_HAVE.match(line)
    if m:
        return ("have", m.group(1), "")
    m = RE_THEOREM.match(s)
    if m:
        return ("theorem", m.group(1), "")
    return None

_HYPS_MARKER = "(by euclid_assumption"

def fold_assumptions(raw):
    idx = raw.find(_HYPS_MARKER)
    if idx < 0:
        return raw, "", 0
    count = raw.count(_HYPS_MARKER)
    return raw[:idx].rstrip(), raw[idx:], count

def parse_main(main_path):
    with open(main_path, encoding="utf-8") as f:
        raw = f.read()
    raw = strip_block_comments(raw)
    lines = raw.splitlines()

    body_start = 0
    for i, l in enumerate(lines):
        if RE_THEOREM.match(l.strip()):
            body_start = i
            break

    result = []
    if body_start > 0:
        result.append({"line": f"-- ({body_start} import / namespace lines)",
                       "kind": "collapsed", "key": None, "role": "sig"})

    # Main is always in tactic-body mode; theorem line itself is sig
    i = body_start
    in_body = False
    while i < len(lines):
        l = lines[i]; i += 1
        if not in_body and (RE_BY.search(l.rstrip()) or RE_BY_ALONE.match(l)):
            in_body = True; role = "sig"
        else:
            role = "body" if in_body else "sig"
        cl = classify_line(l)
        if cl:
            kind, key, _ = cl
            if kind == "sentence" and key is None:
                buf = l; j = i
                while j < len(lines) and ":=" not in buf:
                    nxt = strip_line_comment(lines[j]).rstrip()
                    if not nxt.strip(): break
                    buf += " " + nxt.strip(); j += 1
                cm = RE_CLAIM.search(buf)
                if cm: key = cm.group(1)
            result.append({"line": l, "kind": kind, "key": key, "role": role})
        else:
            result.append({"line": l, "kind": "plain", "key": None, "role": role})
    return result

RE_BY        = re.compile(r':=\s*by\s*$')
RE_BY_ALONE  = re.compile(r'^\s*by\s*$')

def parse_step(path):
    with open(path, encoding="utf-8") as f:
        raw = f.read()
    raw = strip_block_comments(raw)
    lines = raw.splitlines()
    start = 0
    for i, l in enumerate(lines):
        if RE_THEOREM.match(l.strip()):
            start = i; break
    result = []
    in_body = False
    for l in lines[start:]:
        # transition to proof body when we hit `:= by` at end of a line
        if not in_body and (RE_BY.search(l.rstrip()) or RE_BY_ALONE.match(l)):
            in_body = True
            role = "sig"
        else:
            role = "body" if in_body else "sig"
        cl = classify_line(l)
        if cl:
            kind, key, _ = cl
            result.append({"line": l, "kind": kind, "key": key, "role": role})
        else:
            result.append({"line": l, "kind": "plain", "key": None, "role": role})
    child_keys = [it["key"] for it in result if it["kind"] == "have" and it["key"]]
    return result, child_keys

# ── card tree ─────────────────────────────────────────────────────────────────

class Card:
    __slots__ = ("key", "depth", "kind", "lines", "children")
    def __init__(self, key, depth, kind, lines):
        self.key = key; self.depth = depth; self.kind = kind
        self.lines = lines; self.children = []

MAX_FULL_DEPTH = 3

def build_card(key, propdir, depth, kind, visited):
    path = os.path.join(propdir, key + ".lean")
    if not os.path.isfile(path): return None
    absp = os.path.abspath(path)
    if absp in visited: return None
    visited.add(absp)
    lines, child_keys = parse_step(path)
    card = Card(key, depth, kind, lines)
    if depth < MAX_FULL_DEPTH:
        for ck in child_keys:
            child = build_card(ck, propdir, depth + 1, "have", visited)
            if child: card.children.append(child)
    return card

def build_tree(propdir, main_lines):
    visited = set(); roots = []
    for item in main_lines:
        if item["kind"] == "sentence" and item["key"]:
            card = build_card(item["key"], propdir, 1, "sentence", visited)
            if card: roots.append(card)
    return roots

def collect_node_keys(roots):
    """All step keys that have actual backing files (i.e. are real cards)."""
    keys = set()
    def gather(card):
        keys.add(card.key)
        for c in card.children: gather(c)
    for r in roots: gather(r)
    return keys

# ── HTML rendering ────────────────────────────────────────────────────────────

_uid = [0]

def h(s): return htmllib.escape(str(s))

def render_line_content(raw_line):
    visible, hidden, count = fold_assumptions(raw_line)
    if count == 0:
        return h(raw_line)
    _uid[0] += 1; uid = _uid[0]
    noun = "hyp" if count == 1 else "hyps"
    return (
        f"{h(visible)}"
        f'<button class="hyp-btn" data-uid="{uid}" data-n="{count}" data-noun="{noun}" '
        f'onclick="toggleHyp(this)" title="{count} assumption(s)">'
        f'[{count}&nbsp;{noun}&nbsp;&#9658;]</button>'
        f'<span class="hyp-body" id="hb{uid}" style="display:none">{h(hidden)}</span>'
    )

def render_code_lines(items, id_prefix="", node_keys=None):
    out = ""; real_ln = 0
    for item in items:
        k    = item["kind"]
        role = item.get("role", "body")
        if k == "collapsed":
            out += f'<div class="code-line collapsed" data-role="sig"><span class="ln"></span>{h(item["line"])}</div>\n'
            continue
        real_ln += 1
        key = item.get("key")
        content = render_line_content(item["line"])
        ln_text = real_ln if item["line"].strip() else ""
        is_node = key and (node_keys is None or key in node_keys)
        if k in ("sentence", "have") and is_node:
            sid = f'{id_prefix}{key}'
            out += (f'<div class="code-line {k}" data-role="{role}" id="{sid}" '
                    f'data-connects="{key}" data-kind="{k}">'
                    f'<span class="ln">{real_ln}</span>{content}</div>\n')
        else:
            out += (f'<div class="code-line plain" data-role="{role}">'
                    f'<span class="ln">{ln_text}</span>{content}</div>\n')
    return out

def render_card(card, node_keys=None):
    kc  = "sent-card" if card.kind == "sentence" else "have-card"
    nc  = "s"         if card.kind == "sentence" else "h"
    dlb = ["","step","sub-step","sub-sub-step"][min(card.depth, 3)]
    # data-lod starts at "minimal"; JS global buttons override all, per-card button cycles
    out  = f'<div class="card {kc}" id="card-{card.key}" data-lod="minimal">\n'
    out += (f'  <div class="card-header">'
            f'<span class="cname {nc}">{h(card.key)}.lean</span>'
            f'<span class="depth-badge">{dlb}</span>'
            f'<button class="node-lod-btn" onclick="cycleCardLod(this)" title="Toggle detail level">&#9654;</button>'
            f'</div>\n')
    out += '  <div class="card-body">\n'
    out += render_code_lines(card.lines, id_prefix=f"c{card.depth}-", node_keys=node_keys)
    out += '  </div>\n</div>\n'
    return out

# ── page template ─────────────────────────────────────────────────────────────

CSS = """
:root {
  --bg:        #0d0f18;
  --panel:     #13151f;
  --border:    #232636;
  --font:      "JetBrains Mono","Fira Code","Cascadia Code","Menlo",monospace;
  --sz:        12px;
  --lh:        1.65;
  --c-sent:    #52e3c2;
  --c-have:    #f5a623;
  --c-thm:     #7eb6ff;
  --c-plain:   #cdd6f4;
  --c-dimmed:  #454a68;
  --c-bg-sent: rgba(82,227,194,.075);
  --c-bg-have: rgba(245,166,35,.075);
  --c-bg-thm:  rgba(126,182,255,.055);
  --conn-gap:  88px;
  --card-gap:  8px;
  --max-line-w: 9999px;
}
* { box-sizing: border-box; margin: 0; padding: 0; }
html, body { background: var(--bg); }
body {
  color: var(--c-plain);
  font-family: var(--font);
  font-size: var(--sz);
  line-height: var(--lh);
  padding-bottom: 80px;
  /* page scrolls natively — no overflow constraints */
}

/* ── fixed toolbar (stays in view during both X and Y scroll) ── */
.toolbar {
  position: fixed; top: 0; left: 0; right: 0;
  z-index: 200;
  background: #0c0e17;
  border-bottom: 1px solid var(--border);
  padding: 8px 20px;
  display: flex; gap: 28px; align-items: center; flex-wrap: wrap;
}
.toolbar h1 {
  font-size: 13px; font-weight: 600; color: var(--c-thm);
  white-space: nowrap; margin-right: 8px;
}
.ctrl { display: flex; align-items: center; gap: 7px; }
.ctrl label { font-size: 10px; color: var(--c-dimmed); white-space: nowrap; }
.ctrl input[type=range] {
  width: 110px; accent-color: var(--c-sent); cursor: pointer;
}
.ctrl .val {
  font-size: 10.5px; color: #9aa0c0; min-width: 36px;
}
.legend {
  display: flex; gap: 14px; margin-left: auto; flex-wrap: wrap; align-items: center;
}
.leg { display:flex; align-items:center; gap:5px; font-size:9.5px; color:var(--c-dimmed); }
.leg-dot { width:8px; height:8px; border-radius:2px; flex-shrink:0; }

/* ── page body — top padding clears the fixed toolbar ── */
.page { padding: 20px 24px; padding-top: 56px; }

/* ── outer (SVG anchor) ── */
.outer {
  display: flex; gap: 0;
  align-items: flex-start;
  position: relative;
}
#svg-layer {
  position: absolute; top: 0; left: 0;
  pointer-events: none; overflow: visible; z-index: 10;
}

/* ── column header ── */
.col-header {
  padding: 5px 12px;
  background: #181a27;
  border-bottom: 1px solid var(--border);
  font-size: 9px; color: var(--c-dimmed);
  letter-spacing: .08em; text-transform: uppercase;
  white-space: nowrap;
}

/* ── Main.lean panel ── */
.main-col {
  flex: 0 0 auto;
  width: max-content;
  min-width: 200px;
  background: var(--panel);
  border: 1px solid var(--border);
  border-radius: 8px;
  overflow: hidden;       /* clip to card edges cleanly */
  align-self: flex-start;
}
.code-body { padding: 6px 0; }

/* ── code lines ── */
.code-line {
  display: flex;
  align-items: baseline;
  padding: 0 10px;
  white-space: pre;          /* default: never wrap */
}
/* when wrap mode is active (class on <html>), lines wrap at --max-line-w */
html.wrap-lines .code-line {
  white-space: pre-wrap;
  max-width: var(--max-line-w);
  overflow-wrap: break-word;
  word-break: normal;
  /* cards must also stop expanding horizontally */
  overflow-x: hidden;
}
html.wrap-lines .main-col,
html.wrap-lines .card { width: var(--max-line-w); max-width: var(--max-line-w); }

.code-line.plain     { color: var(--c-plain); }
.code-line.collapsed { color: var(--c-dimmed); font-style: italic;
                       white-space: pre-wrap; }   /* always wraps */
.code-line.theorem   { background: var(--c-bg-thm);  color: var(--c-thm);  font-weight: 600; }
.code-line.sentence  { background: var(--c-bg-sent); color: var(--c-sent); }
.code-line.have      { background: var(--c-bg-have); color: var(--c-have); }
.ln {
  flex-shrink: 0; width: 24px;
  color: var(--c-dimmed); font-size: 9px;
  text-align: right; padding-right: 7px;
  user-select: none;
}

/* ── assumption toggle ── */
.hyp-btn {
  display: inline;
  background: #1e2236; border: 1px solid #353b56;
  border-radius: 3px; color: #7a88bb;
  font: var(--sz)/1 var(--font);
  font-size: calc(var(--sz) * 0.83);
  padding: 0 4px; margin-left: 4px;
  cursor: pointer; vertical-align: baseline; white-space: nowrap;
  transition: background .1s, color .1s;
}
.hyp-btn:hover { background: #272d48; color: #aab8e8; }
.hyp-body { color: #666c90; }

/* ── depth columns ── */
.depth-cols { display: flex; gap: 0; align-items: flex-start; }
.depth-col {
  flex: 0 0 auto;
  width: max-content;
  display: flex; flex-direction: column; gap: var(--card-gap);
  padding-left: var(--conn-gap);
}

/* ── cards ── */
.card {
  background: var(--panel);
  border: 1px solid var(--border);
  border-radius: 7px;
  overflow: hidden;          /* clip cleanly; content sets width via max-content */
  width: max-content;
  min-width: 180px;
}
.card.sent-card { border-color: rgba(82,227,194,.20); }
.card.have-card { border-color: rgba(245,166,35,.16); }
.card-header {
  padding: 5px 10px; background: #181a27;
  border-bottom: 1px solid var(--border);
  font-size: 10px; color: var(--c-dimmed);
  display: flex; gap: 6px; align-items: center; white-space: nowrap;
}
.cname       { font-weight: 600; }
.cname.s     { color: var(--c-sent); }
.cname.h     { color: var(--c-have); }
.depth-badge {
  margin-left: auto; font-size: 9px;
  background: #1e2236; color: #444a68;
  padding: 1px 5px; border-radius: 3px;
}
/* card body: NO scroll, NO height cap — show everything */
.card-body { padding: 5px 0; }
.card-body .code-line { font-size: calc(var(--sz) * 0.95); }

/* ── Per-card LOD via data-lod attribute ── */

/* compact: hide tactic body lines, show signature */
[data-lod="compact"] .code-line[data-role="body"] { display: none; }
[data-lod="compact"].card-body { padding-bottom: 2px; }

/* minimal: just the header pill, no body at all */
[data-lod="minimal"] .card-body  { display: none; }
[data-lod="minimal"].card {
  background: none; border-color: transparent; border-radius: 0;
}
[data-lod="minimal"] .card-header {
  background: #1e2236; border: 1px solid #353b56;
  border-radius: 5px; padding: 3px 9px;
}
[data-lod="minimal"] .depth-badge { display: none; }
/* Main col in minimal/compact: same rules */
.main-col[data-lod="compact"] .code-line[data-role="body"] { display: none; }
.main-col[data-lod="minimal"] .code-body { display: none; }

/* ── LOD global buttons ── */
.lod-group { display: flex; gap: 3px; }
.lod-btn {
  background: #1a1d2e; border: 1px solid #353b56;
  border-radius: 4px; color: #5a6080; font: 10px/1 var(--font);
  padding: 3px 8px; cursor: pointer; white-space: nowrap;
  transition: background .1s, color .1s, border-color .1s;
}
.lod-btn:hover  { background: #242840; color: #9aa0c0; }
.lod-btn.active {
  background: #272d48; border-color: var(--c-sent);
  color: var(--c-sent);
}
/* ── per-card cycle button ── */
.node-lod-btn {
  margin-left: auto;
  background: none; border: none;
  color: #3a4060; font: 9px/1 var(--font);
  cursor: pointer; padding: 1px 4px;
  border-radius: 3px;
  transition: color .1s, background .1s;
  flex-shrink: 0;
}
.node-lod-btn:hover { color: #9aa0c0; background: #1e2236; }
/* colour the button to reflect current state */
[data-lod="full"]    .node-lod-btn { color: #52e3c2; }
[data-lod="compact"] .node-lod-btn { color: #f5a623; }
[data-lod="minimal"] .node-lod-btn { color: #3a4060; }
"""

JS = r"""
const root  = document.documentElement;
const svg   = document.getElementById("svg-layer");
const outer = document.querySelector(".outer");

/* ── connectors ── */
function visibleMidRight(el) {
  // Walk up to find the nearest visible ancestor that has real height.
  // A line hidden by display:none has h=0; use its card's header instead.
  let probe = el;
  while (probe) {
    const r = probe.getBoundingClientRect();
    if (r.height > 0) {
      const OR = outer.getBoundingClientRect();
      return { x: r.right - OR.left, y: (r.top + r.bottom) / 2 - OR.top };
    }
    probe = probe.closest(".card-body, .card, .main-col")?.nextElementSibling
            ? null
            : probe.parentElement?.closest(".card, .main-col");
  }
  return null;
}

function drawConnectors() {
  while (svg.firstChild) svg.removeChild(svg.firstChild);
  const OR = outer.getBoundingClientRect();

  document.querySelectorAll("[data-connects]").forEach(src => {
    const card = document.getElementById("card-" + src.dataset.connects);
    if (!card) return;

    // Source anchor: the highlighted line if visible, else the card it lives in
    const srcR = src.getBoundingClientRect();
    let p1;
    if (srcR.height > 0) {
      p1 = { x: srcR.right - OR.left, y: (srcR.top + srcR.bottom) / 2 - OR.top };
    } else {
      // source line is hidden (LOD) — find its containing card and use that
      const srcCard = src.closest(".card, .main-col");
      if (!srcCard) return;
      const scr = srcCard.getBoundingClientRect();
      if (scr.height === 0) return;
      p1 = { x: scr.right - OR.left, y: (scr.top + scr.bottom) / 2 - OR.top };
    }

    // Target anchor: card header (always visible in all LOD modes)
    const hdr = card.querySelector(".card-header");
    const hr  = hdr.getBoundingClientRect();
    if (hr.height === 0) return;
    const p2  = { x: hr.left - OR.left, y: (hr.top + hr.bottom) / 2 - OR.top };

    const dx = Math.max(16, Math.abs(p2.x - p1.x) * 0.42);
    const d  = `M${p1.x},${p1.y} C${p1.x+dx},${p1.y} ${p2.x-dx},${p2.y} ${p2.x},${p2.y}`;
    const path = document.createElementNS("http://www.w3.org/2000/svg","path");
    path.setAttribute("d", d);
    const sent = src.dataset.kind === "sentence";
    path.setAttribute("stroke", sent ? "rgba(82,227,194,.48)" : "rgba(245,166,35,.45)");
    path.setAttribute("stroke-width", "1.6");
    path.setAttribute("fill", "none");
    if (!sent) path.setAttribute("stroke-dasharray", "5 3");
    svg.appendChild(path);
  });

  const tot = outer.getBoundingClientRect();
  svg.setAttribute("width",  Math.ceil(tot.width)  + 2);
  svg.setAttribute("height", Math.ceil(tot.height) + 2);
}

/* ── assumption toggle ── */
function toggleHyp(btn) {
  const body = document.getElementById("hb" + btn.dataset.uid);
  const open = body.style.display !== "none";
  body.style.display = open ? "none" : "inline";
  btn.innerHTML = open
    ? `[${btn.dataset.n}&nbsp;${btn.dataset.noun}&nbsp;&#9658;]`
    : `[${btn.dataset.n}&nbsp;${btn.dataset.noun}&nbsp;&#9660;]`;
  requestAnimationFrame(drawConnectors);
}

/* ── sliders ── */
const szSlider  = document.getElementById("sz-slider");
const lhSlider  = document.getElementById("lh-slider");
const gapSlider = document.getElementById("gap-slider");
const mwSlider  = document.getElementById("mw-slider");
const szVal     = document.getElementById("sz-val");
const lhVal     = document.getElementById("lh-val");
const gapVal    = document.getElementById("gap-val");
const mwVal     = document.getElementById("mw-val");

function applySliders() {
  const sz  = parseFloat(szSlider.value);
  const lh  = parseFloat(lhSlider.value);
  const gap = parseInt(gapSlider.value);
  const mw  = parseInt(mwSlider.value);

  root.style.setProperty("--sz",       sz  + "px");
  root.style.setProperty("--lh",       lh);
  root.style.setProperty("--conn-gap", gap + "px");
  root.style.setProperty("--card-gap", Math.round(gap * 0.12) + "px");

  if (mw >= 2000) {
    // unlimited: remove wrap mode
    root.classList.remove("wrap-lines");
    root.style.setProperty("--max-line-w", "9999px");
    mwVal.textContent = "∞";
  } else {
    root.classList.add("wrap-lines");
    root.style.setProperty("--max-line-w", mw + "px");
    mwVal.textContent = mw + "px";
  }

  szVal.textContent  = sz + "px";
  lhVal.textContent  = lh.toFixed(1) + "×";
  gapVal.textContent = gap + "px";
  requestAnimationFrame(drawConnectors);
}

szSlider.addEventListener("input",  applySliders);
lhSlider.addEventListener("input",  applySliders);
gapSlider.addEventListener("input", applySliders);
mwSlider.addEventListener("input",  applySliders);

/* ── LOD ── */
const LOD_CYCLE = ["minimal", "compact", "full"];

function setCardLod(el, level) {
  el.setAttribute("data-lod", level);
  const btn = el.querySelector(".node-lod-btn");
  if (btn) btn.title = "Current: " + level + " — click to cycle";
}

/* global buttons: apply level to every card + Main */
function setAllLod(level) {
  document.querySelectorAll(".card, .main-col").forEach(c => setCardLod(c, level));
  document.querySelectorAll(".lod-btn").forEach(b =>
    b.classList.toggle("active", b.dataset.lod === level));
  requestAnimationFrame(drawConnectors);
}

/* per-card cycle button: minimal → compact → full → minimal */
function cycleCardLod(btn) {
  const card = btn.closest(".card, .main-col");
  const cur  = card.getAttribute("data-lod") || "minimal";
  const next = LOD_CYCLE[(LOD_CYCLE.indexOf(cur) + 1) % LOD_CYCLE.length];
  setCardLod(card, next);
  requestAnimationFrame(drawConnectors);
}

/* initial draw */
window.addEventListener("load", () => {
  applySliders();
  drawConnectors();
});
window.addEventListener("resize", drawConnectors);
"""

def build_html(prop_name, main_lines, roots):
    node_keys = collect_node_keys(roots)

    cols = {}
    def gather(card):
        cols.setdefault(card.depth, []).append(card)
        for c in card.children: gather(c)
    for r in roots: gather(r)

    main_html  = '<div class="main-col" data-lod="full">\n'
    main_html += ('<div class="col-header">Main.lean'
                  '<button class="node-lod-btn" onclick="cycleCardLod(this)" title="Toggle detail level">&#9654;</button>'
                  '</div>\n')
    main_html += '<div class="code-body">\n'
    main_html += render_code_lines(main_lines, node_keys=node_keys)
    main_html += '</div></div>\n'

    dcols = '<div class="depth-cols">\n'
    for depth in sorted(cols.keys()):
        lbl = ["","Step files","Sub-step files","Sub-sub-step files"][min(depth, 3)]
        dcols += '<div class="depth-col">\n'
        dcols += f'<div class="col-header">{lbl}</div>\n'
        for card in cols[depth]:
            dcols += render_card(card, node_keys=node_keys)
        dcols += '</div>\n'
    dcols += '</div>\n'

    return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>Proof map — {h(prop_name)}</title>
<style>{CSS}</style>
</head>
<body>
<div class="toolbar">
  <h1>Proof map — {h(prop_name)}</h1>
  <div class="ctrl">
    <label for="sz-slider">Font</label>
    <input type="range" id="sz-slider" min="9" max="20" step="0.5" value="12">
    <span class="val" id="sz-val">12px</span>
  </div>
  <div class="ctrl">
    <label for="lh-slider">Row&nbsp;height</label>
    <input type="range" id="lh-slider" min="1.0" max="3.2" step="0.1" value="1.65">
    <span class="val" id="lh-val">1.7×</span>
  </div>
  <div class="ctrl">
    <label for="gap-slider">Node&nbsp;gap</label>
    <input type="range" id="gap-slider" min="40" max="400" step="10" value="88">
    <span class="val" id="gap-val">88px</span>
  </div>
  <div class="ctrl">
    <label for="mw-slider">Max&nbsp;width</label>
    <input type="range" id="mw-slider" min="200" max="2000" step="50" value="2000">
    <span class="val" id="mw-val">&#8734;</span>
  </div>
  <div class="lod-group">
    <button class="lod-btn"        data-lod="full"    onclick="setAllLod('full')">Full</button>
    <button class="lod-btn"        data-lod="compact" onclick="setAllLod('compact')">Compact</button>
    <button class="lod-btn active" data-lod="minimal" onclick="setAllLod('minimal')">Minimal</button>
  </div>
  <div class="legend">
    <div class="leg"><div class="leg-dot" style="background:#7eb6ff"></div>theorem</div>
    <div class="leg"><div class="leg-dot" style="background:#52e3c2"></div>euclid_sentence</div>
    <div class="leg"><div class="leg-dot" style="background:#f5a623"></div>have node (dashed)</div>
    <div class="leg" style="color:#7a88bb">&#9658; = assumptions folded</div>
  </div>
</div>
<div class="page">
<div class="outer">
  <svg id="svg-layer"></svg>
  {main_html}
  {dcols}
</div>
</div>
<script>
{JS}
</script>
</body>
</html>
"""

# ── CLI ───────────────────────────────────────────────────────────────────────

def export_pdf(html_path):
    pdf = os.path.splitext(html_path)[0] + ".pdf"
    for exe in ("google-chrome","chromium","chromium-browser"):
        try:
            subprocess.run([exe,"--headless","--disable-gpu",
                            f"--print-to-pdf={pdf}","--print-to-pdf-no-header",
                            "--no-margins", f"file://{os.path.abspath(html_path)}"],
                           check=True, capture_output=True)
            print(f"wrote {pdf}"); return
        except (FileNotFoundError, subprocess.CalledProcessError):
            continue
    print("PDF: use Chrome → Print → Save as PDF.")

def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--prop", required=True)
    ap.add_argument("-o","--out")
    ap.add_argument("--pdf", action="store_true")
    args = ap.parse_args()

    propdir = args.prop
    if not os.path.isdir(propdir):
        alt = os.path.join("LeanEuclidPlus", propdir)
        if os.path.isdir(alt): propdir = alt
        else: sys.exit(f"folder not found: {args.prop}")

    main_path = os.path.join(propdir, "Main.lean")
    if not os.path.isfile(main_path):
        sys.exit(f"no Main.lean in {propdir}")

    _uid[0] = 0
    main_lines = parse_main(main_path)
    roots      = build_tree(propdir, main_lines)
    prop_name  = os.path.basename(propdir.rstrip("/\\"))

    out = args.out or os.path.join(propdir, "map.html")
    with open(out, "w", encoding="utf-8") as f:
        f.write(build_html(prop_name, main_lines, roots))
    print(f"wrote {out}")
    if args.pdf: export_pdf(out)

if __name__ == "__main__":
    main()
