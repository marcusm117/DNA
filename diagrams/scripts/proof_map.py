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

# ── Lean syntax highlighter ───────────────────────────────────────────────────

# ── Lean syntax highlighter (single regex pass, runs in C) ───────────────────

_KW_CLASS = {
    "theorem":"kw-def","lemma":"kw-def","def":"kw-def","abbrev":"kw-def",
    "instance":"kw-def","namespace":"kw-def","end":"kw-def","open":"kw-def",
    "import":"kw-def","section":"kw-def","structure":"kw-def","class":"kw-def",
    "by":"kw-by",
    "have":"kw-have","let":"kw-have",
    "show":"kw-tac","exact":"kw-tac","apply":"kw-tac","rw":"kw-tac",
    "simp":"kw-tac","ring":"kw-tac","linarith":"kw-tac","assumption":"kw-tac",
    "intro":"kw-tac","intros":"kw-tac","cases":"kw-tac","induction":"kw-tac",
    "constructor":"kw-tac","refine":"kw-tac","push_neg":"kw-tac",
    "contrapose":"kw-tac","contradiction":"kw-tac",
    "euclid_intros":"kw-euclid","euclid_finish":"kw-euclid",
    "euclid_apply":"kw-euclid","euclid_assumption":"kw-euclid",
    "euclid_sentence":"kw-sent","euclid_intro_sentence":"kw-sent",
    "euclid_conclude_sentence":"kw-sent",
    "fun":"kw-quant","match":"kw-quant","if":"kw-quant","then":"kw-quant","else":"kw-quant",
    "true":"kw-bool","false":"kw-bool","True":"kw-bool","False":"kw-bool",
    "sorry":"kw-sorry",
}

# One compiled regex: alternatives are tried left-to-right by the C engine.
_HL_RE = re.compile(
    r'("(?:[^"\\]|\\.)*")'           # group 1: string literal
    r'|(\b(?:' + '|'.join(re.escape(k) for k in sorted(_KW_CLASS, key=len, reverse=True)) + r')\b)'
                                      # group 2: keyword (longest first)
    r'|([a-zA-Z_]\w*(?::[a-zA-Z_]\w*)+)'  # group 3: point-colon chain a:b:c (match before bare :)
    r'|(:=|=>|[→←↔])'                # group 4: arrow/assign ops
    r'|([∧∨¬∥⊥])'                    # group 5: logic ops
    r'|([=≠≤≥])'                      # group 6: relation ops
    r'|([∟△─∠∀∃])'                   # group 7: special math
    r'|(:)'                           # group 8: colon
    r'|([([{⟨])'                      # group 9: open bracket
    r'|([\])}⟩])'                     # group 10: close bracket
    r'|(\b\d[\d.]*\b)'                # group 11: number
)

_GRP_CLASS = {
    1: "t-str",
    2: None,       # keyword — dict lookup
    3: "t-id",     # point-colon chain a:b:c — plain identifier
    4: "op-assign", 5: "op-logic", 6: "op-rel", 7: "op-special",
    8: "op-colon", 9: "t-brk-o", 10: "t-brk-c", 11: "t-num",
}

def lean_highlight(raw):
    """Return HTML with Lean syntax highlighting — single regex pass."""
    def repl(m):
        for g, cls in _GRP_CLASS.items():
            if m.group(g) is not None:
                text = htmllib.escape(m.group(g))
                if g == 2:
                    cls = _KW_CLASS.get(m.group(g), "t-id")
                return f'<span class="{cls}">{text}</span>'
        return htmllib.escape(m.group(0))
    # escape everything not matched, then apply regex substitution
    # We do it in one pass: split on matches, escape gaps, wrap matches.
    result = []
    last = 0
    for m in _HL_RE.finditer(raw):
        if m.start() > last:
            result.append(htmllib.escape(raw[last:m.start()]))
        result.append(repl(m))
        last = m.end()
    if last < len(raw):
        result.append(htmllib.escape(raw[last:]))
    return "".join(result)

# ── HTML rendering ────────────────────────────────────────────────────────────

_uid = [0]

def h(s): return htmllib.escape(str(s))

def render_line_content(raw_line):
    """Highlight then fold assumptions."""
    visible, hidden, count = fold_assumptions(raw_line)
    # highlight both parts
    vis_html = lean_highlight(visible)
    if count == 0:
        return lean_highlight(raw_line)
    _uid[0] += 1; uid = _uid[0]
    noun = "hyp" if count == 1 else "hyps"
    hid_html = lean_highlight(hidden)
    return (
        f"{vis_html}"
        f'<button class="hyp-btn" data-uid="{uid}" data-n="{count}" data-noun="{noun}" '
        f'onclick="toggleHyp(this)" title="{count} assumption(s)">'
        f'[{count}&nbsp;{noun}&nbsp;&#9658;]</button>'
        f'<span class="hyp-body" id="hb{uid}" style="display:none">{hid_html}</span>'
    )

def render_code_lines(items, id_prefix="", node_keys=None):
    out = ""; real_ln = 0
    for item in items:
        k    = item["kind"]
        role = item.get("role", "body")
        if k == "collapsed":
            out += (f'<div class="code-line collapsed" data-role="sig">'
                    f'<span class="ln"></span><span class="lc">{h(item["line"])}</span></div>\n')
            continue
        # emit blank lines so euclid_sentence blocks are separated
        if not item["line"].strip():
            out += (f'<div class="code-line plain" data-role="{role}">'
                    f'<span class="ln"></span><span class="lc"> </span></div>\n')
            continue
        real_ln += 1
        key = item.get("key")
        content = render_line_content(item["line"])
        is_node = key and (node_keys is None or key in node_keys)
        if k in ("sentence", "have") and is_node:
            sid = f'{id_prefix}{key}'
            out += (f'<div class="code-line {k}" data-role="{role}" id="{sid}" '
                    f'data-connects="{key}" data-kind="{k}">'
                    f'<span class="ln">{real_ln}</span><span class="lc">{content}</span></div>\n')
        else:
            out += (f'<div class="code-line plain" data-role="{role}">'
                    f'<span class="ln">{real_ln}</span><span class="lc">{content}</span></div>\n')
    return out

def render_card(card, node_keys=None):
    kc  = "sent-card" if card.kind == "sentence" else "have-card"
    nc  = "s"         if card.kind == "sentence" else "h"
    dlb = ["","step","sub-step","sub-sub-step"][min(card.depth, 3)]
    # data-lod starts at "minimal"; JS global buttons override all, per-card button cycles
    out  = f'<div class="card {kc}" id="card-{card.key}" data-lod="minimal">\n'
    out += (f'  <div class="card-header">'
            f'<span class="hdr-left"  data-sel="parents"><span class="hdr-arrow">&#9668;</span></span>'
            f'<span class="hdr-center">'
            f'<span class="cname {nc}">{h(card.key)}.lean</span>'
            f'<span class="depth-badge">{dlb}</span>'
            f'<button class="node-lod-btn" onclick="cycleCardLod(this)" title="Toggle detail level">&#9654;</button>'
            f'</span>'
            f'<span class="hdr-right" data-sel="children"><span class="hdr-arrow">&#9658;</span></span>'
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
  --title-sz:  11px;
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
.page { padding: 60px 48px 80px; padding-top: 72px; }

/* ── outer (SVG anchor) ── */
.outer {
  display: flex; gap: 0;
  align-items: flex-start;
  position: relative;
  /* top / bottom / left margin around the graph */
  padding: 40px 0 60px 40px;
}
#svg-layer {
  position: absolute; top: 0; left: 0;
  pointer-events: none; overflow: visible; z-index: 10;
}

/* ── Lean syntax colours ── */
.kw-def    { color: #c792ea; font-weight: 600; }  /* theorem/lemma/def/import */
.kw-by     { color: #89ddff; font-weight: 600; }  /* by */
.kw-have   { color: #f5a623; font-weight: 600; }  /* have/let */
.kw-tac    { color: #82aaff; }                     /* exact/apply/rw/simp/linarith … */
.kw-euclid { color: #21c7a8; font-weight: 600; }  /* euclid_apply/finish/intros */
.kw-sent   { color: #52e3c2; font-weight: 600; }  /* euclid_sentence */
.kw-quant  { color: #c792ea; }                     /* ∀/∃/fun/match */
.kw-bool   { color: #f78c6c; }                     /* true/false */
.kw-sorry  { color: #ff5370; font-weight: 700; background: rgba(255,83,112,.12);
             padding: 0 2px; border-radius: 2px; }
.op-assign { color: #89ddff; }   /* := */
.op-arrow  { color: #89ddff; }   /* → ← ↔ => */
.op-logic  { color: #c792ea; }   /* ∧ ∨ ¬ */
.op-rel    { color: #89ddff; }   /* = ≠ ≤ ≥ */
.op-colon  { color: #89ddff; }   /* : */
.op-special{ color: #ffcb6b; }   /* ∟ △ ─ ∠ */
.t-str     { color: #c3e88d; }   /* "string literals" */
.t-num     { color: #f78c6c; }   /* numbers */
.t-id      { color: var(--c-plain); }
.t-brk-o   { color: #ffcb6b; }   /* ( [ { ⟨ */
.t-brk-c   { color: #ffcb6b; }   /* ) ] } ⟩ */

/* ── column header ── */
.col-header {
  background: #181a27;
  border-bottom: 1px solid var(--border);
  font-size: var(--title-sz); color: #8090b8;
  font-weight: 600; letter-spacing: .05em; text-transform: uppercase;
  white-space: nowrap;
  /* 3-zone grid: left-zone | center | right-zone */
  display: grid;
  grid-template-columns: 1fr auto 1fr;
  align-items: center;
  min-height: calc(var(--title-sz) * 2.4);
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
}
/* .lc = line content: one flex child that owns all text + wrapping */
.lc {
  white-space: pre;          /* never wrap by default */
  flex: 1;
  min-width: 0;
}
/* wrap mode: only .lc wraps, never at span boundaries */
html.wrap-lines .lc {
  white-space: pre-wrap;
  overflow-wrap: anywhere;   /* break long tokens, not at span edges */
  word-break: normal;
  max-width: var(--max-line-w);
}
html.wrap-lines .main-col,
html.wrap-lines .card { width: var(--max-line-w); max-width: var(--max-line-w); }

.code-line.plain     { color: var(--c-plain); }
.code-line.collapsed { color: var(--c-dimmed); font-style: italic; }
.code-line.collapsed .lc { white-space: pre-wrap; }
/* theorem/sentence/have: background tint only — syntax spans control text color */
.code-line.theorem  { background: var(--c-bg-thm); }
.code-line.sentence { background: var(--c-bg-sent); }
.code-line.have     { background: var(--c-bg-have); }
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
.depth-cols { display: flex; gap: 0; align-items: flex-start; padding-right: 60px; }
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
  background: #181a27;
  border-bottom: 1px solid var(--border);
  font-size: var(--title-sz); color: #8090b8;
  white-space: nowrap;
  /* 3-zone grid: left-zone | center | right-zone */
  display: grid;
  grid-template-columns: 1fr auto 1fr;
  align-items: center;
  min-height: calc(var(--title-sz) * 2.4);
}
/* center zone: name + LOD button, centered */
.hdr-center {
  display: flex; gap: 5px; align-items: center; justify-content: center;
  padding: calc(var(--title-sz) * 0.35) 6px;
}
.cname   { font-weight: 700; font-size: var(--title-sz); }
.cname.s { color: #6ef5d8; }   /* brighter teal for step files */
.cname.h { color: #ffc04d; }   /* brighter orange for sub-step files */
.depth-badge { display: none; }
/* left and right click zones */
.hdr-left, .hdr-right {
  display: flex; align-items: center;
  padding: 4px 6px;
  height: 100%;
  user-select: none;
  transition: background .12s, color .12s;
}
.hdr-left  { justify-content: flex-start; cursor: w-resize; }
.hdr-right { justify-content: flex-end;   cursor: e-resize; }
.hdr-left:hover  { background: rgba(180,140,255,.10); color: rgba(180,140,255,.80); }
.hdr-right:hover { background: rgba(82,227,194,.08);  color: rgba(82,227,194,.70); }
.hdr-arrow {
  font-size: 9px; opacity: 0.35;
  transition: opacity .12s, transform .12s;
}
.hdr-left:hover  .hdr-arrow { opacity: 0.85; transform: scale(1.2); }
.hdr-right:hover .hdr-arrow { opacity: 0.85; transform: scale(1.2); }
/* selected state tints */
.selected .hdr-left  { color: rgba(180,140,255,.65); }
.selected .hdr-right { color: rgba(82,227,194,.65); }
/* card body: NO scroll, NO height cap — show everything */
.card-body { padding: 5px 0; }
.card-body .code-line { font-size: calc(var(--sz) * 0.95); }

/* ── selection: card glow — colour depends on card type ── */
.card.sent-card.selected, .main-col.selected {
  box-shadow: 0 0 0 2px rgba(82,227,194,.90), 0 0 20px rgba(82,227,194,.22);
  z-index: 20;
}
.card.have-card.selected {
  box-shadow: 0 0 0 2px rgba(245,166,35,.90), 0 0 20px rgba(245,166,35,.22);
  z-index: 20;
}
.card.sent-card.selected .card-header, .main-col.selected .col-header {
  background: rgba(82,227,194,.10);
}
.card.have-card.selected .card-header {
  background: rgba(245,166,35,.10);
}

/* ── child-highlight: target card of a selected connection ── */
.card.sent-card.child-highlight {
  box-shadow: 0 0 0 1.5px rgba(82,227,194,.55), 0 0 10px rgba(82,227,194,.12);
}
.card.have-card.child-highlight {
  box-shadow: 0 0 0 1.5px rgba(245,166,35,.55), 0 0 10px rgba(245,166,35,.12);
}
/* ── parent-highlight: source card of an incoming connection ── */
.card.parent-highlight, .main-col.parent-highlight {
  box-shadow: 0 0 0 1.5px rgba(180,140,255,.60), 0 0 10px rgba(180,140,255,.14);
}
/* ── parent source lines (incoming edges to selected card) ── */
.code-line.sel-parent-line {
  background: rgba(180,140,255,.12) !important;
  outline: 1px solid rgba(180,140,255,.40);
  cursor: pointer;
}
/* left/right halves of header show appropriate cursor hints */
.card-header { cursor: grab; }
.col-header  { cursor: grab; }

/* ── sel-line: a [data-connects] line that is currently selected ── */
.code-line.sel-line {
  background: rgba(255,230,80,.11) !important;
  outline: 1px solid rgba(255,230,80,.38);
  cursor: pointer;
}
/* all [data-connects] lines are clickable when hovered */
.code-line[data-connects]:hover {
  background: rgba(255,255,255,.04) !important;
  cursor: pointer;
}

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

/* suppress text selection while dragging */
body.dragging { user-select: none; }

/* ── rubber-band selection rect ── */
#rband {
  position: fixed;
  border: 1px solid rgba(82,227,194,.7);
  background: rgba(82,227,194,.07);
  pointer-events: none;
  display: none;
  z-index: 100;
}

/* ── layout controls ── */
.export-group {
  display: flex; gap: 8px; align-items: center;
  border-left: 1px solid var(--border);
  padding-left: 16px; margin-left: 4px;
}
.save-btn {
  background: #1e2a1e; border: 1px solid rgba(82,227,194,.35);
  border-radius: 4px; color: var(--c-sent);
  font: 10px/1 var(--font); padding: 4px 10px; cursor: pointer;
  white-space: nowrap; transition: background .1s;
}
.save-btn:hover { background: #253225; }
.reset-btn {
  background: #221a1a; border: 1px solid rgba(200,80,80,.30);
  border-radius: 4px; color: #c87070;
  font: 10px/1 var(--font); padding: 4px 10px; cursor: pointer;
  white-space: nowrap; transition: background .1s;
}
.reset-btn:hover { background: #2e1a1a; }

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

// ── selection state ──────────────────────────────────────────────────────────
// selCards: Map<element, mode>  where mode = "children" | "parents"
const selCards = new Map();
const selLines = new Set();  // selected [data-connects] line elements
let suppressNextClear = false;  // set after rubber-band to block the trailing click

// Outgoing lines from a card → child cards
function getLinesFrom(card) {
  return Array.from(card.querySelectorAll("[data-connects]"));
}
function getChildCards(card) {
  return getLinesFrom(card).map(l => document.getElementById("card-" + l.dataset.connects)).filter(Boolean);
}

// All [data-connects] lines anywhere on the page that point TO this card
function getParentLines(card) {
  const key = card.id.replace(/^card-/, "");
  return key ? Array.from(document.querySelectorAll(`[data-connects="${key}"]`)) : [];
}
function getParentCards(card) {
  return getParentLines(card)
    .map(l => l.closest(".card, .main-col"))
    .filter((c, i, a) => c && a.indexOf(c) === i);
}

function applyCardHighlights(card, mode, add) {
  const fn = add ? "add" : "remove";
  card.classList[fn]("selected");
  if (mode === "children") {
    getChildCards(card).forEach(c => c.classList[fn]("child-highlight"));
  } else {
    getParentCards(card).forEach(c => c.classList[fn]("parent-highlight"));
    getParentLines(card).forEach(l => l.classList[fn]("sel-parent-line"));
  }
}

function clearSelection() {
  selCards.forEach((mode, card) => applyCardHighlights(card, mode, false));
  selCards.clear();
  selLines.forEach(l => {
    l.classList.remove("sel-line");
    const t = document.getElementById("card-" + l.dataset.connects);
    if (t) t.classList.remove("child-highlight");
  });
  selLines.clear();
  drawConnectors();
}

function selectCard(card, mode, additive) {
  if (!additive) {
    // normal click: clear all, then select just this one
    // but if it's the only selected card with same mode, toggle off
    if (selCards.size === 1 && selCards.get(card) === mode) {
      clearSelection(); return;
    }
    clearSelection();
  } else {
    // shift-click: toggle this card
    if (selCards.has(card) && selCards.get(card) === mode) {
      applyCardHighlights(card, mode, false);
      selCards.delete(card);
      drawConnectors(); return;
    }
    // if already selected in other mode, remove old highlights first
    if (selCards.has(card)) {
      applyCardHighlights(card, selCards.get(card), false);
      selCards.delete(card);
    }
    // line selections stay when additively selecting cards
  }
  selCards.set(card, mode);
  applyCardHighlights(card, mode, true);
  drawConnectors();
}

function selectLine(lineEl, additive) {
  if (!additive) {
    if (selLines.size === 1 && selLines.has(lineEl) && selCards.size === 0) {
      clearSelection(); return;  // toggle off single
    }
    clearSelection();
  }
  if (additive && selLines.has(lineEl)) {
    // toggle this line out
    lineEl.classList.remove("sel-line");
    const t = document.getElementById("card-" + lineEl.dataset.connects);
    if (t) t.classList.remove("child-highlight");
    selLines.delete(lineEl);
    drawConnectors(); return;
  }
  selLines.add(lineEl);
  lineEl.classList.add("sel-line");
  const target = document.getElementById("card-" + lineEl.dataset.connects);
  if (target) target.classList.add("child-highlight");
  drawConnectors();
}

// ── connectors ───────────────────────────────────────────────────────────────

function anchorRight(el) {
  const OR = outer.getBoundingClientRect();
  let probe = el;
  while (probe) {
    const r = probe.getBoundingClientRect();
    if (r.height > 0) return { x: r.right - OR.left, y: (r.top + r.bottom) / 2 - OR.top };
    probe = probe.parentElement?.closest(".card, .main-col") ?? null;
  }
  return null;
}

function drawConnectors() {
  while (svg.firstChild) svg.removeChild(svg.firstChild);
  const OR = outer.getBoundingClientRect();

  document.querySelectorAll("[data-connects]").forEach(src => {
    const card = document.getElementById("card-" + src.dataset.connects);
    if (!card) return;

    const p1 = anchorRight(src);
    if (!p1) return;

    const hdr = card.querySelector(".card-header, .col-header");
    if (!hdr || hdr.getBoundingClientRect().height === 0) return;
    const hr = hdr.getBoundingClientRect();
    const p2 = { x: hr.left - OR.left, y: (hr.top + hr.bottom) / 2 - OR.top };

    // Active if: exact selected line, OR source card selected (children mode),
    // OR this is an incoming edge to a card selected in parents mode.
    const isActiveLine = selLines.has(src);
    const srcCard      = src.closest(".card, .main-col");
    const srcMode      = srcCard ? selCards.get(srcCard) : undefined;
    const srcSelected  = srcMode === "children";
    const tgtMode      = selCards.get(card);
    const isParentEdge = tgtMode === "parents" && srcCard !== card;
    const isActive     = isActiveLine || srcSelected || isParentEdge;

    // Colour: parent edges purple, child/line edges teal or orange
    const sent  = src.dataset.kind === "sentence";
    let baseC;
    if (isActive && isParentEdge) baseC = [180, 140, 255];
    else if (sent)                 baseC = [82,  227, 194];
    else                           baseC = [245, 166,  35];
    const alpha = isActive ? 0.95 : 0.32;
    const color = `rgba(${baseC[0]},${baseC[1]},${baseC[2]},${alpha})`;
    const width = isActive ? "2.4" : "1.4";

    const dx = Math.max(16, Math.abs(p2.x - p1.x) * 0.42);
    const d  = `M${p1.x},${p1.y} C${p1.x+dx},${p1.y} ${p2.x-dx},${p2.y} ${p2.x},${p2.y}`;
    const path = document.createElementNS("http://www.w3.org/2000/svg", "path");
    path.setAttribute("d", d);
    path.setAttribute("stroke", color);
    path.setAttribute("stroke-width", width);
    path.setAttribute("fill", "none");
    if (!sent) path.setAttribute("stroke-dasharray", isActive ? "none" : "5 3");
    if (isActive) path.setAttribute("filter", `drop-shadow(0 0 4px ${color})`);
    svg.appendChild(path);
  });

  const tot = outer.getBoundingClientRect();
  svg.setAttribute("width",  Math.ceil(tot.width)  + 2);
  svg.setAttribute("height", Math.ceil(tot.height) + 2);
}

// ── drag + click on card header ───────────────────────────────────────────────
const DRAG_THRESHOLD = 5;

function getTranslate(elem) {
  const t = elem.style.transform;
  const m = t && t.match(/translate\(\s*([-\d.]+)px,\s*([-\d.]+)px\)/);
  return m ? [parseFloat(m[1]), parseFloat(m[2])] : [0, 0];
}

function initDragSelect(el) {
  const hdr = el.querySelector(".card-header, .col-header");
  if (!hdr) return;

  let startX, startY, dragging = false;
  // snapshot of every selected card's translate at drag-start
  let groupSnaps = null;

  hdr.addEventListener("mousedown", e => {
    if (e.target.closest("button")) return;
    startX = e.clientX; startY = e.clientY;
    dragging = false;
    const zone = e.target.closest("[data-sel]");
    const downMode = zone ? zone.dataset.sel : null;

    function onMove(e) {
      const dx = e.clientX - startX, dy = e.clientY - startY;
      if (!dragging && Math.hypot(dx, dy) > DRAG_THRESHOLD) {
        dragging = true;
        // if this card is selected, snapshot the whole group; else just this card
        if (selCards.has(el)) {
          groupSnaps = new Map();
          selCards.forEach((_, card) => groupSnaps.set(card, getTranslate(card)));
        } else {
          groupSnaps = new Map([[el, getTranslate(el)]]);
        }
        document.body.classList.add("dragging");
        groupSnaps.forEach((_, card) => {
          card.style.position = "relative";
          card.style.zIndex   = "50";
        });
      }
      if (dragging) {
        groupSnaps.forEach(([tx, ty], card) => {
          card.style.transform = `translate(${tx + dx}px,${ty + dy}px)`;
        });
        drawConnectors();
      }
    }

    function onUp(e) {
      document.removeEventListener("mousemove", onMove);
      document.removeEventListener("mouseup",   onUp);
      document.body.classList.remove("dragging");
      if (groupSnaps) groupSnaps.forEach((_, card) => card.style.zIndex = "");
      groupSnaps = null;
      if (!dragging) {
        e.stopPropagation();
        selectCard(el, downMode || "children", e.ctrlKey || e.metaKey);
      }
    }

    document.addEventListener("mousemove", onMove);
    document.addEventListener("mouseup",   onUp);
    e.preventDefault();
  });
}

// ── rubber-band selection on empty canvas ─────────────────────────────────────
function initRubberBand() {
  const rband = document.getElementById("rband");
  let rbX, rbY, active = false;

  document.addEventListener("mousedown", e => {
    // skip card/toolbar interactive elements
    if (e.target.closest(".card-header, .col-header, .toolbar, button, input, select, label")) return;
    if (e.button !== 0) return;
    e.preventDefault();  // block text selection unconditionally
    rbX = e.clientX; rbY = e.clientY;
    active = false;
    e.preventDefault();  // block text selection from the start

    function onMove(e) {
      const dx = e.clientX - rbX, dy = e.clientY - rbY;
      if (!active && Math.hypot(dx, dy) > DRAG_THRESHOLD) {
        active = true;
        rband.style.display = "block";
        document.body.classList.add("dragging");
      }
      if (active) {
        rband.style.left   = Math.min(e.clientX, rbX) + "px";
        rband.style.top    = Math.min(e.clientY, rbY) + "px";
        rband.style.width  = Math.abs(dx) + "px";
        rband.style.height = Math.abs(dy) + "px";
      }
    }

    function onUp(e) {
      document.removeEventListener("mousemove", onMove);
      document.removeEventListener("mouseup",   onUp);
      rband.style.display = "none";
      document.body.classList.remove("dragging");
      if (!active) return;
      suppressNextClear = true;  // prevent the click handler from wiping the selection

      // collect all cards whose headers overlap the rubber-band rect
      const r1 = {
        l: Math.min(e.clientX, rbX), r: Math.max(e.clientX, rbX),
        t: Math.min(e.clientY, rbY), b: Math.max(e.clientY, rbY),
      };
      const additive = e.ctrlKey || e.metaKey;
      if (!additive) clearSelection();

      document.querySelectorAll(".card, .main-col").forEach(card => {
        const hdr = card.querySelector(".card-header, .col-header");
        if (!hdr) return;
        const r2 = hdr.getBoundingClientRect();
        const overlaps = r1.l < r2.right && r1.r > r2.left &&
                         r1.t < r2.bottom && r1.b > r2.top;
        if (overlaps && !selCards.has(card)) {
          selCards.set(card, "children");
          applyCardHighlights(card, "children", true);
        }
      });
      drawConnectors();
    }

    document.addEventListener("mousemove", onMove);
    document.addEventListener("mouseup",   onUp);
  });
}

// ── assumption toggle ─────────────────────────────────────────────────────────
function toggleHyp(btn) {
  const body = document.getElementById("hb" + btn.dataset.uid);
  const open = body.style.display !== "none";
  body.style.display = open ? "none" : "inline";
  btn.innerHTML = open
    ? `[${btn.dataset.n}&nbsp;${btn.dataset.noun}&nbsp;&#9658;]`
    : `[${btn.dataset.n}&nbsp;${btn.dataset.noun}&nbsp;&#9660;]`;
  requestAnimationFrame(drawConnectors);
}

// ── sliders ───────────────────────────────────────────────────────────────────
const tszSlider = document.getElementById("tsz-slider");
const szSlider  = document.getElementById("sz-slider");
const lhSlider  = document.getElementById("lh-slider");
const gapSlider = document.getElementById("gap-slider");
const mwSlider  = document.getElementById("mw-slider");
const tszVal    = document.getElementById("tsz-val");
const szVal     = document.getElementById("sz-val");
const lhVal     = document.getElementById("lh-val");
const gapVal    = document.getElementById("gap-val");
const mwVal     = document.getElementById("mw-val");

function applySliders() {
  const tsz = parseFloat(tszSlider.value);
  const sz  = parseFloat(szSlider.value);
  const lh  = parseFloat(lhSlider.value);
  const gap = parseInt(gapSlider.value);
  const mw  = parseInt(mwSlider.value);

  root.style.setProperty("--title-sz",  tsz + "px");
  root.style.setProperty("--sz",        sz  + "px");
  root.style.setProperty("--lh",        lh);
  root.style.setProperty("--conn-gap",  gap + "px");
  root.style.setProperty("--card-gap",  Math.round(gap * 0.12) + "px");

  if (mw >= 2000) {
    root.classList.remove("wrap-lines");
    root.style.setProperty("--max-line-w", "9999px");
    mwVal.textContent = "∞";
  } else {
    root.classList.add("wrap-lines");
    root.style.setProperty("--max-line-w", mw + "px");
    mwVal.textContent = mw + "px";
  }

  tszVal.textContent = tsz + "px";
  szVal.textContent  = sz + "px";
  lhVal.textContent  = lh.toFixed(1) + "×";
  gapVal.textContent = gap + "px";
  requestAnimationFrame(drawConnectors);
}

tszSlider.addEventListener("input", applySliders);
szSlider.addEventListener("input",  applySliders);
lhSlider.addEventListener("input",  applySliders);
gapSlider.addEventListener("input", applySliders);
mwSlider.addEventListener("input",  applySliders);

// ── LOD ───────────────────────────────────────────────────────────────────────
const LOD_CYCLE = ["minimal", "compact", "full"];

function setCardLod(el, level) {
  el.setAttribute("data-lod", level);
}

function setAllLod(level) {
  document.querySelectorAll(".card, .main-col").forEach(c => setCardLod(c, level));
  document.querySelectorAll(".lod-btn").forEach(b =>
    b.classList.toggle("active", b.dataset.lod === level));
  requestAnimationFrame(drawConnectors);
}

function cycleCardLod(btn) {
  const card = btn.closest(".card, .main-col");
  const cur  = card.getAttribute("data-lod") || "minimal";
  const next = LOD_CYCLE[(LOD_CYCLE.indexOf(cur) + 1) % LOD_CYCLE.length];
  setCardLod(card, next);
  requestAnimationFrame(drawConnectors);
}

// ── layout save / load / reset ────────────────────────────────────────────────
const LAYOUT_KEY = "proof_map_layout_" + document.title.replace(/[^a-zA-Z0-9]/g, "_");

function saveLayout() {
  const state = { cards: {}, lod: {}, sliders: {} };
  document.querySelectorAll(".card, .main-col").forEach(el => {
    const id = el.id || "main-col";
    state.cards[id] = getTranslate(el);
    state.lod[id]   = el.getAttribute("data-lod") || "minimal";
  });
  state.sliders = {
    tsz: parseFloat(tszSlider.value),
    sz:  parseFloat(szSlider.value),
    lh:  parseFloat(lhSlider.value),
    gap: parseInt(gapSlider.value),
    mw:  parseInt(mwSlider.value),
  };
  const json = JSON.stringify(state, null, 2);
  localStorage.setItem(LAYOUT_KEY, json);
  // Also download as a file so headless export can use it
  const blob = new Blob([json], {type: "application/json"});
  const a = document.createElement("a");
  a.href = URL.createObjectURL(blob);
  a.download = "map_layout.json";
  a.click();
  URL.revokeObjectURL(a.href);
  const btn = document.getElementById("save-btn");
  const orig = btn.textContent;
  btn.textContent = "Saved ✓";
  setTimeout(() => btn.textContent = orig, 1200);
}

function loadLayout() {
  let state = window.__LAYOUT__ || null;
  if (!state) {
    const raw = localStorage.getItem(LAYOUT_KEY);
    if (!raw) return;
    try { state = JSON.parse(raw); } catch { return; }
  }

  if (state.sliders) {
    if (state.sliders.tsz != null) tszSlider.value = state.sliders.tsz;
    if (state.sliders.sz  != null) szSlider.value  = state.sliders.sz;
    if (state.sliders.lh  != null) lhSlider.value  = state.sliders.lh;
    if (state.sliders.gap != null) gapSlider.value = state.sliders.gap;
    if (state.sliders.mw  != null) mwSlider.value  = state.sliders.mw;
    applySliders();
  }

  document.querySelectorAll(".card, .main-col").forEach(el => {
    const id = el.id || "main-col";
    if (state.cards && state.cards[id]) {
      const [tx, ty] = state.cards[id];
      if (tx !== 0 || ty !== 0) {
        el.style.position  = "relative";
        el.style.transform = `translate(${tx}px,${ty}px)`;
      }
    }
    if (state.lod && state.lod[id]) {
      el.setAttribute("data-lod", state.lod[id]);
    }
  });
  drawConnectors();
}

function resetLayout() {
  localStorage.removeItem(LAYOUT_KEY);
  document.querySelectorAll(".card, .main-col").forEach(el => {
    el.style.transform = "";
    el.style.position  = "";
    el.setAttribute("data-lod", el.classList.contains("main-col") ? "full" : "minimal");
  });
  tszSlider.value = 11; szSlider.value = 12; lhSlider.value = 1.65; gapSlider.value = 88; mwSlider.value = 2000;
  applySliders();
  drawConnectors();
}

// ── import layout from file ──────────────────────────────────────────────────
function importLayout() {
  document.getElementById("import-file").click();
}
document.getElementById("import-file").addEventListener("change", e => {
  const file = e.target.files[0];
  if (!file) return;
  const reader = new FileReader();
  reader.onload = () => {
    try {
      window.__LAYOUT__ = JSON.parse(reader.result);
      loadLayout();
    } catch (err) { alert("Invalid layout JSON: " + err.message); }
  };
  reader.readAsText(file);
  e.target.value = "";
});

// ── init ──────────────────────────────────────────────────────────────────────
window.addEventListener("load", () => {
  document.querySelectorAll(".card, .main-col").forEach(initDragSelect);

  document.querySelectorAll("[data-connects]").forEach(lineEl => {
    lineEl.addEventListener("click", e => {
      if (e.target.closest("button")) return;
      e.stopPropagation();
      selectLine(lineEl, e.ctrlKey || e.metaKey);
    });
  });

  initRubberBand();
  applySliders();
  loadLayout();      // restore saved positions/sliders/LOD if any
  drawConnectors();

  document.addEventListener("click", e => {
    if (suppressNextClear) { suppressNextClear = false; return; }
    if (!e.target.closest(".card, .main-col")) clearSelection();
  });
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
    main_html += ('<div class="col-header">'
                  '<span class="hdr-left"  data-sel="parents"><span class="hdr-arrow">&#9668;</span></span>'
                  '<span class="hdr-center">Main.lean'
                  '<button class="node-lod-btn" onclick="cycleCardLod(this)" title="Toggle detail level">&#9654;</button>'
                  '</span>'
                  '<span class="hdr-right" data-sel="children"><span class="hdr-arrow">&#9658;</span></span>'
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
    <label for="tsz-slider">Title</label>
    <input type="range" id="tsz-slider" min="9" max="32" step="0.5" value="11">
    <span class="val" id="tsz-val">11px</span>
  </div>
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
  <div class="export-group">
    <button id="save-btn" class="save-btn" onclick="saveLayout()">Save layout</button>
    <button class="save-btn" onclick="importLayout()">Import layout</button>
    <input type="file" id="import-file" accept=".json" style="display:none">
    <button class="reset-btn" onclick="resetLayout()">Reset</button>
  </div>
  <div class="legend">
    <div class="leg"><div class="leg-dot" style="background:#7eb6ff"></div>theorem</div>
    <div class="leg"><div class="leg-dot" style="background:#52e3c2"></div>euclid_sentence</div>
    <div class="leg"><div class="leg-dot" style="background:#f5a623"></div>have node (dashed)</div>
    <div class="leg" style="color:#7a88bb">Shift+click = multi-select</div>
  </div>
</div>
<div id="rband"></div>
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

def export_png(html_path, scale=2, transparent=False):
    from playwright.sync_api import sync_playwright

    png_path = os.path.splitext(html_path)[0] + ".png"
    layout_path = os.path.join(os.path.dirname(html_path), "map_layout.json")

    layout_json = None
    if os.path.isfile(layout_path):
        with open(layout_path) as f:
            layout_json = f.read()

    with sync_playwright() as p:
        browser = p.chromium.launch()
        # Inject layout before page loads
        page = browser.new_page(device_scale_factor=scale)
        if layout_json:
            page.add_init_script(f"window.__LAYOUT__ = {layout_json};")
        page.goto("file://" + os.path.abspath(html_path))
        page.wait_for_load_state("networkidle")
        page.evaluate("document.querySelector('.toolbar').style.display = 'none'")
        page.evaluate("document.querySelector('.page').style.paddingTop = '20px'")
        page.evaluate("drawConnectors()")
        page.wait_for_timeout(100)
        content_size = page.evaluate("""() => {
            const o = document.querySelector('.outer');
            return { width: o.scrollWidth + 100, height: o.scrollHeight + 100 };
        }""")
        page.set_viewport_size(content_size)
        page.evaluate("drawConnectors()")
        page.wait_for_timeout(50)
        page.screenshot(path=png_path, full_page=True, omit_background=transparent)
        browser.close()
    src = "layout" if layout_json else "defaults"
    print(f"wrote {png_path} ({scale}x, {src})")

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
    ap.add_argument("--png", action="store_true", help="Export PNG via headless browser")
    ap.add_argument("--scale", type=int, default=2, help="PNG resolution multiplier (default 2)")
    ap.add_argument("--transparent", action="store_true", help="Transparent PNG background")
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
    if args.png: export_png(out, scale=args.scale, transparent=args.transparent)

if __name__ == "__main__":
    main()
