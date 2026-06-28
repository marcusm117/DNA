#!/usr/bin/env python3
"""
Plot the proof-tree structure of a LeanEuclidPlus proposition.

Our codebase organizes proofs as a tree:

    Main (theorem)                     <- root
     |-- euclid_sentence "2.11.1"      <- child of Main
     |-- euclid_sentence "2.11.8"
     |      +-- have step8_bisect      <- child of the sentence
     |      +-- have step8_pyth
     |             +-- have ...        <- subtree, and so on (recursion)
     ...

A `theorem`/`lemma` is the root.  Every `have` or `euclid_sentence` is a child of
its container.  `have`s nest inside `by` blocks by indentation, so the tree is
recovered by an indentation-stack descent over the source.

Two modes:
  --file PATH        parse a single .lean file's internal tree.
  --prop PROPN       parse a whole proposition folder: Main.lean is the root,
                     each euclid_sentence is a child, and (recursively) each
                     node whose name has a backing file <name>.lean in the
                     folder is expanded into that file's tree.  This stitches
                     the cross-file decomposition into one picture.

Output: Graphviz `dot` -> SVG + PNG next to the source (override with -o).

USAGE
  python3 diagrams/scripts/plot_tree.py --prop Book2/Prop11
  python3 diagrams/scripts/plot_tree.py --file LeanEuclidPlus/Book2/Prop11/step8.lean
"""

import argparse
import os
import re
import subprocess
import sys

# ---------------------------------------------------------------------------
# tree model
# ---------------------------------------------------------------------------

class Node:
    __slots__ = ("name", "kind", "detail", "children", "file_key")

    def __init__(self, name, kind, detail="", file_key=None):
        self.name = name          # short label (theorem name, sentence id, have name)
        self.kind = kind          # 'theorem' | 'sentence' | 'have' | 'file'
        self.detail = detail      # one-line extra info (truncated claim type / text)
        self.children = []
        self.file_key = file_key  # backing-file stem to expand from in --prop mode

    def show(self, depth=0):
        pad = "  " * depth
        print(f"{pad}{self.kind}: {self.name}  {self.detail}")
        for c in self.children:
            c.show(depth + 1)


# ---------------------------------------------------------------------------
# lexing helpers
# ---------------------------------------------------------------------------

def strip_block_comments(text):
    """Remove /- ... -/ block comments (may span lines)."""
    return re.sub(r"/-.*?-/", "", text, flags=re.DOTALL)


def strip_line_comment(line):
    """Remove a -- line comment (naive: ignores -- inside strings; fine here)."""
    # don't trip on the `─`/`-` unicode; -- is two ASCII hyphens.
    idx = -1
    for i in range(len(line) - 1):
        if line[i] == "-" and line[i + 1] == "-":
            idx = i
            break
    return line if idx < 0 else line[:idx]


# opener regexes (run against the stripped, dedented code of a line)
RE_THEOREM = re.compile(r"^(?:theorem|lemma|def)\s+(\S+)")
RE_HAVE    = re.compile(r"^have\s+(\S+)\s*(?::=|:)")
RE_SENT    = re.compile(r"^euclid_\w*sentence\s+\"([^\"]*)\"")
RE_CLAIM   = re.compile(r"\((\w+)\s*:")   # (stepN : Type) inside a sentence line


def opener(code):
    """Return (kind, name) if this line opens a node, else None."""
    m = RE_THEOREM.match(code)
    if m:
        return ("theorem", m.group(1).rstrip(":"))
    m = RE_SENT.match(code)
    if m:
        return ("sentence", m.group(1))
    m = RE_HAVE.match(code)
    if m:
        return ("have", m.group(1))
    return None


def short(s, n=34):
    s = " ".join(str(s).split())
    if len(s) <= n:
        return s
    return s[: n - 1].rstrip() + "…"


def sanitize(s):
    """Keep DOT/label-safe ASCII; replace exotic glyphs so PNG doesn't tofu."""
    out = []
    for ch in s:
        o = ord(ch)
        if ch in "\\":
            out.append("\\\\")
        elif ch == '"':
            out.append("'")
        elif o < 128:
            out.append(ch)
        elif ch in "─│┌┐└┘∟∠△□∀∃¬∧∨→←≠∥⊥≅≤≥≡·∙":
            out.append(ch)
        else:
            out.append("?")
    return "".join(out)


# ---------------------------------------------------------------------------
# single-file parser (indentation-stack descent)
# ---------------------------------------------------------------------------

def parse_file(path):
    with open(path, encoding="utf-8") as fh:
        raw = fh.read()
    raw = strip_block_comments(raw)
    lines = raw.splitlines()

    file_root = Node(os.path.basename(path), "file")
    stack = [(-1, file_root)]   # (indent, node); virtual root at indent -1

    i = 0
    while i < len(lines):
        line = strip_line_comment(lines[i]).rstrip()
        i += 1
        if not line.strip():
            continue
        indent = len(line) - len(line.lstrip(" "))
        code = line.strip()
        kind = opener(code)
        if kind is None:
            continue
        kname, name = kind

        # Buffer continuation lines through the terminating ':=' so we can read
        # the (stepN : Type) claim group of a multi-line euclid_sentence.
        stmt = code
        while ":=" not in stmt and i < len(lines):
            nxt = strip_line_comment(lines[i]).rstrip()
            if not nxt.strip():
                break
            if opener(nxt.strip()) is not None:   # don't swallow a sibling node
                break
            stmt += " " + nxt.strip()
            i += 1

        # pop until parent has strictly smaller indent
        while stack and stack[-1][0] >= indent:
            stack.pop()
        parent = stack[-1][1]

        detail = ""
        file_key = None
        if kname == "have":
            # type text is between the first ':' and ':='
            seg = stmt.split(":=", 1)[0]
            seg = seg.split(":", 1)[1] if ":" in seg else ""
            detail = short(sanitize(seg.strip()))
            file_key = name
        elif kname == "sentence":
            cm = RE_CLAIM.search(stmt)
            file_key = cm.group(1) if cm else None
            detail = f"[{file_key}]" if file_key else "(claim inline)"
        elif kname == "theorem":
            detail = ""

        node = Node(name, kname, detail, file_key)
        parent.children.append(node)
        stack.append((indent, node))

    # collapse: drop the synthetic 'file' wrapper, return its single theorem child
    # (or the wrapper itself if the file defines several/none).
    real = [c for c in file_root.children if c.kind == "theorem"]
    if len(real) == 1:
        return real[0]
    return file_root


# ---------------------------------------------------------------------------
# prop-folder stitcher
# ---------------------------------------------------------------------------

def expand(node, propdir, visited):
    """Attach backing-file subtrees to every node that has one, recursively."""
    key = node.file_key
    if key:
        cand = os.path.join(propdir, key + ".lean")
        if os.path.isfile(cand) and os.path.abspath(cand) not in visited:
            visited.add(os.path.abspath(cand))
            sub = parse_file(cand)
            # the backing file's theorem's haves become this node's children
            kids = sub.children if sub.kind == "theorem" else [sub]
            for k in kids:
                node.children.append(k)
    # always descend, whether or not this node itself expanded
    for c in list(node.children):
        expand(c, propdir, visited)


def parse_prop(propdir):
    main = os.path.join(propdir, "Main.lean")
    if not os.path.isfile(main):
        sys.exit(f"no Main.lean in {propdir}")
    root = parse_file(main)
    expand(root, propdir, set([os.path.abspath(main)]))
    return root


# ---------------------------------------------------------------------------
# Graphviz rendering
# ---------------------------------------------------------------------------

KIND_STYLE = {
    "theorem": ("#1f3b73", "#cfe0ff", "bold"),
    "sentence": ("#0b6b5b", "#cdf3ec", ""),
    "have":     ("#5b3b00", "#fbe6c4", ""),
    "file":     ("#444444", "#e8e8e8", ""),
}


def esc(s):
    return sanitize(s).replace("\\", "\\\\")


def to_dot(root, max_depth=None, rankdir="LR"):
    lines = [
        "digraph proof {",
        f"  rankdir={rankdir};",
        "  graph [fontname=\"Helvetica\", nodesep=0.18, ranksep=0.45];",
        '  node  [fontname="Helvetica", shape=box, style="rounded,filled", '
        'margin="0.10,0.06", penwidth=1.1];',
        '  edge  [color="#7a7a7a", arrowsize=0.7];',
    ]
    counter = [0]

    def nid():
        counter[0] += 1
        return f"n{counter[0]}"

    def walk(node, depth):
        me = nid()
        fc, bg, weight = KIND_STYLE.get(node.kind, KIND_STYLE["have"])
        label = node.name
        if node.detail:
            label = f"{label}\\n{node.detail}" if node.name else node.detail
        lines.append(
            f'  {me} [label="{esc(label)}", fillcolor="{bg}", '
            f'color="{fc}", fontcolor="{fc}", fontweight="{weight}"];'
        )
        if max_depth is not None and depth >= max_depth:
            if node.children:
                more = nid()
                lines.append(f'  {more} [label="…", shape=none, fillcolor=none];')
                lines.append(f"  {me} -> {more};")
            return me
        for c in node.children:
            child = walk(c, depth + 1)
            lines.append(f"  {me} -> {child};")
        return me

    walk(root, 0)
    lines.append("}")
    return "\n".join(lines)


def render(dot_text, outbase):
    svg = outbase + ".svg"
    png = outbase + ".png"
    for path, fmt in ((svg, "svg"), (png, "png")):
        try:
            subprocess.run(
                ["dot", f"-T{fmt}", "-o", path],
                input=dot_text.encode("utf-8"),
                check=True,
            )
        except FileNotFoundError:
            sys.exit("graphviz `dot` not found on PATH; install graphviz.")
        except subprocess.CalledProcessError as e:
            sys.exit(f"dot failed ({fmt}): {e}")
    print(f"wrote {svg}")
    print(f"wrote {png}")


# ---------------------------------------------------------------------------
# cli
# ---------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--file", help="a single .lean file to plot")
    g.add_argument("--prop", help="a proposition folder (contains Main.lean)")
    ap.add_argument("-o", "--out", help="output basename (no extension)")
    ap.add_argument("--max-depth", type=int, default=None,
                    help="cap tree depth (rest collapsed to …)")
    ap.add_argument("--rankdir", default="LR", choices=["LR", "TB"],
                    help="layout direction: LR (left-right, default) or TB (top-bottom)")
    ap.add_argument("--text", action="store_true",
                    help="also print the tree as indented text")
    args = ap.parse_args()

    if args.file:
        path = args.file
        if not os.path.isfile(path):
            # try under LeanEuclidPlus/
            alt = os.path.join("LeanEuclidPlus", path)
            if os.path.isfile(alt):
                path = alt
            else:
                sys.exit(f"file not found: {args.file}")
        root = parse_file(path)
        default_out = os.path.splitext(path)[0]
    else:
        propdir = args.prop
        if not os.path.isdir(propdir):
            alt = os.path.join("LeanEuclidPlus", propdir)
            if os.path.isdir(alt):
                propdir = alt
            else:
                sys.exit(f"prop folder not found: {args.prop}")
        root = parse_prop(propdir)
        # nicer root label for the prop picture
        root.name = os.path.basename(propdir.rstrip("/")) + "  (Main)"
        root.detail = ""
        default_out = os.path.join(propdir, "tree")

    outbase = args.out or default_out
    if args.text:
        root.show()
        print()

    dot_text = to_dot(root, args.max_depth, args.rankdir)
    render(dot_text, outbase)


if __name__ == "__main__":
    main()
