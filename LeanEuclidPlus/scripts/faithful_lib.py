#!/usr/bin/env python3
"""Shared library for the faithful pipeline (Phase B verify + Phase C wire). NO CLI — imported by
`check_step.py` and `wire_main.py`.

THE MODEL (see the plan / the faithful-prove skill). Everything is ONE recursive atom:
  * CONTAINER  = any .lean file with a tactic proof holding goal nodes (Main.lean, stepN.lean, a
                 sub-file, …). A container may also hold REAL euclid_apply proof work — that is not a
                 node and is never touched.
  * GOAL NODE  = a named `:= by sorry` body. Two surface forms, identical at the proof level:
                   - Main only:  euclid_sentence "loc" "txt" (stepN : C) := by sorry
                   - anywhere :  have <name> : C := by sorry
  * BACKING FILE = the helper proving a node.  NAMING LAW (enforced, abort-loud):
                   node name  ≡  <name>.lean basename  ≡  theorem helper_<book>_<name>.
  * WIRING     = a node's `sorry` replaced by the canonical
                   euclid_apply (helper_<book>_<name> <objs>); euclid_finish
                 where <objs> = the Point/Line/Circle binder names of the backing theorem, in order.
                 ONLY scripts ever write wiring; the agent only writes proof bodies + adds sorry-`have`s.

Bodies on disk are ALWAYS one canonical single-line shape (the only shapes this lib reads/writes):
    := by sorry
    := by trace_state; sorry                              (transient, --context only)
    := by euclid_apply (helper_<book>_<name> …); euclid_finish
A fixed-shape text swap on these (no tactic parsing) ⟹ false positives are structurally impossible.

Caps: every file carries `set_option systemE.solverTime 30 in` above its theorem in the dev state.
Phase C (`wire_main`) deletes it (→ System E's 300s default — strictly MORE time, never less).
"""
import os, re, sys, glob, signal, subprocess, fcntl

# ── locations / constants ─────────────────────────────────────────────────────────────────────────
# realpath (not just abspath): the repo is reachable via both /h/56/taddmao/… and /u/taddmao/… (a
# symlink). If BOOK_ROOT and an incoming path resolve through different roots, os.path.relpath yields a
# garbage `../../../u/…` Lean target. Canonicalizing both ends here makes every relpath/target_of sound.
BOOK_ROOT = os.path.realpath(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))   # LeanEuclidPlus/
DEFAULT_VENV = os.path.expanduser("~/.venvs/leaneuclid")
GEOMETRIC_SORTS = {"Point", "Line", "Circle"}      # the only `axiom … : Type` object sorts (Sorts/Primitives.lean)
CAP_LINE = "set_option systemE.solverTime 30 in"
CAP_SECONDS = 30                                    # the ONE allowed dev SMT cap (also the wall, below)
# CAP_RE matches ANY solverTime line (used to strip/detect a cap regardless of value).
CAP_RE   = re.compile(r"^[ \t]*set_option[ \t]+systemE\.solverTime[ \t]+\d+[ \t]+in[ \t]*\r?\n", re.MULTILINE)
# CAP_RE_EXACT matches ONLY the canonical 30s cap — `--check` requires this exact value so a bumped
# `solverTime 300` is flagged (the wall still kills it, but the structural guard should catch it too).
CAP_RE_EXACT = re.compile(r"^[ \t]*set_option[ \t]+systemE\.solverTime[ \t]+" + str(CAP_SECONDS) +
                          r"[ \t]+in[ \t]*\r?\n", re.MULTILINE)
WALL = CAP_SECONDS                                  # seconds — the per-build wall timeout (dev only)


class FaithfulError(Exception):
    """Any structural/naming/canonical-shape violation. Callers print it and exit non-zero — the
    scripts ABORT LOUDLY rather than guess or proceed on a malformed prop."""


# tokens that "fake" a proof — none may appear except a node's own canonical `:= by sorry` body.
CHEAT_RE = re.compile(r"\b(sorry|admit|native_decide|sorryAx)\b|@\[[^\]]*\]\s*axiom\b|^\s*axiom\b", re.MULTILINE)


def blank_comments(src: str) -> str:
    """Replace Lean `--` line and `/- … -/` block comments with same-length spaces (newlines kept), so
    a token inside a comment (e.g. the word 'sorry' in a `-- @args:`/explanatory note) is not matched
    while character offsets stay aligned with the original. Mirrors check_signatures.py:strip_comments."""
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        two = src[i:i+2]
        if depth == 0 and two == "--":
            while i < n and src[i] != "\n":
                out.append(" "); i += 1
            continue
        if two == "/-":
            depth += 1; out.append("  "); i += 2; continue
        if two == "-/" and depth > 0:
            depth -= 1; out.append("  "); i += 2; continue
        if depth > 0:
            out.append("\n" if src[i] == "\n" else " "); i += 1; continue
        out.append(src[i]); i += 1
    return "".join(out)


def natural_key(s):
    """Sort key so `step2` < `step10` (numeric runs compared as ints, not lexicographically)."""
    return [int(t) if t.isdigit() else t for t in re.split(r"(\d+)", s)]


# ── path / target helpers ─────────────────────────────────────────────────────────────────────────
def resolve(arg):
    """A path relative to LeanEuclidPlus/ (or absolute) → absolute, REALPATH-canonicalized (so an
    alternate symlinked root collapses onto BOOK_ROOT — see the BOOK_ROOT note)."""
    return os.path.realpath(arg if os.path.isabs(arg) else os.path.join(BOOK_ROOT, arg))


def propdir_of(arg):
    """Accept `Book2/Prop04`, `Book2/Prop04/`, or `Book2/Prop04/Main.lean` → absolute prop dir."""
    p = resolve(arg)
    if p.endswith(".lean"):
        p = os.path.dirname(p)
    p = p.rstrip("/")
    if not os.path.isdir(p):
        raise FaithfulError(f"no such prop directory: {arg}")
    if not os.path.exists(os.path.join(p, "Main.lean")):
        raise FaithfulError(f"{os.path.relpath(p, BOOK_ROOT)} has no Main.lean — not a prop folder")
    return p


import contextlib


@contextlib.contextmanager
def prop_lock(propdir, *, block=True):
    """An exclusive PER-PROP lock so only ONE check_step/wire_main runs against a given prop at a time.
    Different props lock on different files → still fully parallel; the SAME prop serializes (a second
    runner waits, or aborts loudly if block=False). This guards the WHOLE swap→build→revert window
    (the file edits, not just the `lake build`), closing the lost-update race where two runs editing the
    same Main.lean clobber each other. The lock lives under `.lake/` (already git-ignored, so no stray
    file in the prop folder), keyed by the prop's path."""
    key = os.path.relpath(propdir, BOOK_ROOT).replace(os.sep, "_")
    lock_dir = os.path.join(BOOK_ROOT, ".lake", "faithful-locks")
    os.makedirs(lock_dir, exist_ok=True)
    lock_path = os.path.join(lock_dir, f"{key}.lock")
    rel = os.path.relpath(propdir, BOOK_ROOT)
    f = open(lock_path, "w")
    try:
        if block:
            try:                                          # fast path: grab it immediately if free
                fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:                       # contended → announce, then wait
                print(f"[lock] {rel} is held by another check_step/wire_main — waiting for it to "
                      f"finish (only one runner per prop)…", flush=True)
                fcntl.flock(f, fcntl.LOCK_EX)
                print(f"[lock] acquired {rel} — proceeding.", flush=True)
        else:
            try:
                fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                raise FaithfulError(
                    f"another check_step/wire_main is already running on {rel} — only one at a time "
                    f"per prop. Wait for it to finish, or run a DIFFERENT prop.")
        yield
    finally:
        fcntl.flock(f, fcntl.LOCK_UN)
        f.close()


def book_num(propdir):
    """`…/Book2/Prop04` → 2.  The <book> in helper_<book>_<name>."""
    for part in os.path.relpath(propdir, BOOK_ROOT).split(os.sep):
        m = re.fullmatch(r"Book(\d+)", part)
        if m:
            return int(m.group(1))
    raise FaithfulError(f"cannot determine book number from {os.path.relpath(propdir, BOOK_ROOT)}")


def main_file(propdir):
    return os.path.join(propdir, "Main.lean")


def prop_files(propdir):
    """Every .lean file in the prop folder tree (Main + all backing/sub files), sorted."""
    return sorted(glob.glob(os.path.join(propdir, "**", "*.lean"), recursive=True))


def target_of(path):
    """File path → Lean build target: rel to BOOK_ROOT, '/'→'.', drop '.lean'.
    Book2/Prop04/step27.lean → Book2.Prop04.step27 ; nested step27/big.lean → Book2.Prop04.step27.big."""
    rel = os.path.relpath(os.path.realpath(path), BOOK_ROOT)
    return rel[:-len(".lean")].replace(os.sep, ".")


def depth_of(path, propdir):
    """How deep below the prop folder a file sits (Main = 0)."""
    rel = os.path.relpath(os.path.realpath(path), os.path.realpath(propdir))
    return rel.count(os.sep)


def _containment(propdir):
    """Return (occs, children, book): the node occurrences, and `children[name]` = the sub-node NAMES
    defined inside name's backing file (the backing-file containment relation). Keyed by NAME, so a
    shared helper's single backing file is visited ONCE even though the name has many occurrences."""
    occs = parse_occurrences(propdir)
    book = book_num(propdir)
    children = {}
    for name in occs:
        bf = backing_file(propdir, name)
        kids = [k.name for k in parse_nodes_in_file(bf, book)] if bf else []
        children[name] = [k for k in kids if k in occs]
    return occs, children, book


def _bottom_up(occs, children, roots):
    """Topological (post-order) bottom-up walk over `children` from `roots`: a node whose backing file
    contains sub-nodes comes AFTER all of those sub-nodes, so the FIRST failure in a sweep is always the
    DEEPEST broken node. Returns the REACHABLE node NAMES in bottom-up order (each once). Deterministic
    via natural_key. Raises on a cyclic containment."""
    ordered, seen = [], set()
    def visit(name, stack):
        if name in seen:
            return
        if name in stack:
            raise FaithfulError(f"cyclic backing-file dependency through '{name}'")
        for kid in children.get(name, []):
            visit(kid, stack | {name})
        seen.add(name)
        ordered.append(name)
    for name in sorted(roots, key=natural_key):
        visit(name, frozenset())
    return ordered


def audit_order(propdir):
    """ALL nodes, bottom-up: `[(name, [all occurrences]) …]`. (sub-nodes before their parents; the real
    proof-tree depth, NOT directory depth — a sub-node often lives in a sibling file.)"""
    occs, children, _ = _containment(propdir)
    return [(name, occs[name]) for name in _bottom_up(occs, children, occs.keys())]


def cone_names(propdir, root):
    """The set of node names in Cone(root): root + everything transitively contained in root's backing
    file (its sub-nodes, recursively). Raises FaithfulError if `root` isn't a node."""
    occs, children, _ = _containment(propdir)
    if root not in occs:
        raise FaithfulError(f"no node '{root}' in {os.path.relpath(propdir, BOOK_ROOT)}")
    return set(_bottom_up(occs, children, {root}))


def subtree_order(propdir, root):
    """Cone(root) in bottom-up order, with each node's occurrences SCOPED TO THE CONE: a shared helper's
    SP is checked only at call sites whose container file is INSIDE this cone (root's backing file or a
    descendant's), NOT at its uses in other steps. So `--subtree step27` checks `positions@step27` but
    not `positions@step9`. Returns `[(name, [in-cone occurrences]) …]`; P (once per name) is unaffected
    (same single backing file regardless of cone). Raises if `root` isn't a node."""
    occs, children, _ = _containment(propdir)
    if root not in occs:
        raise FaithfulError(f"no node '{root}' in {os.path.relpath(propdir, BOOK_ROOT)}")
    names = _bottom_up(occs, children, {root})
    # An occurrence is IN THE CONE iff its container file is the backing file of some cone node (root's
    # backing file or a descendant's) — that's where all sub-node call sites live. The ROOT node itself
    # is wired at ITS OWN call site (e.g. step27 in Main), so root keeps all its occurrences. This is
    # what scopes a shared helper to this cone: `positions@step27` (container step27.lean ∈ cone) is
    # checked; `positions@step9` (container step9.lean ∉ cone) is not.
    cone_files = {os.path.realpath(backing_file(propdir, n)) for n in names if backing_file(propdir, n)}
    out = []
    for name in names:
        if name == root:
            scoped = occs[name]                       # root: checked at its own call site(s)
        else:
            scoped = [nd for nd in occs[name] if os.path.realpath(nd.file) in cone_files]
        out.append((name, scoped))
    return out


# ── low-level scanners (mirror scripts/check_steps.py) ──────────────────────────────────────────────
def _skip_string(src, i, n):
    """`src[i]` is the opening `"` — return the index just past the closing quote."""
    i += 1
    while i < n and src[i] != '"':
        i += 2 if src[i] == "\\" else 1
    return i + 1


def balanced_paren(src, start):
    """`start` is the index just AFTER an already-open `(` (depth 1). Return the index of its matching
    `)` (the close), skipping nested parens + string literals."""
    depth, i, n = 1, start, len(src)
    while i < n:
        c = src[i]
        if c == '"':
            i = _skip_string(src, i, n); continue
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                return i
        i += 1
    raise FaithfulError("unbalanced parentheses while scanning")


def type_until_assign(src, start):
    """For a bare `have name : <type> := …`: `start` is just after the type-separator `:`. Scan to the
    first top-level `:=` (respecting () [] {} and strings; angle/area colons like `∠ b:a:d` are plain
    `:` and ignored). Return (type_text, index_of_`:=`)."""
    depth, i, n = 0, start, len(src)
    while i < n:
        c = src[i]
        if c == '"':
            i = _skip_string(src, i, n); continue
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif depth == 0 and c == ":" and i + 1 < n and src[i + 1] == "=":
            return src[start:i], i
        i += 1
    raise FaithfulError("no `:=` found for a `have` (malformed node?)")


# ── canonical body matching / swapping ──────────────────────────────────────────────────────────────
def _body_regexes(book, name):
    """The three canonical body shapes for a node, anchored at the `:=`. The WIRED shape requires the
    called helper to be THIS node's own helper (helper_<book>_<name>) — so a real proof-local `have`
    that merely calls some *other* helper is NOT mistaken for a wired node."""
    helper = re.escape(f"helper_{book}_{name}")
    # Separators between successive tactics may be `;`, a newline, or both — so a wired body is
    # recognized whether it was written single-line (canonical, by wire_main) or multiline (legacy
    # finished props). The helper-name anchor keeps a *different* helper's call from matching.
    return [
        ("sorry", re.compile(r":=[ \t]*by[ \t\r\n]+sorry\b")),
        ("trace", re.compile(r":=[ \t]*by[ \t\r\n]+trace_state[ \t\r\n]*;[ \t\r\n]*sorry\b")),
        # The arg list may contain ONE level of nested parens — the `(by assumption)` hypothesis args
        # the wire emits (full application). `(?:[^()]|\([^()]*\))*` matches flat chars OR a nested
        # `(…)` group, so the closing `)` is the helper-call's own. Without this, a wired body with
        # `(by assumption)` would not be recognized and integrity_scan/wire_main would mis-handle it.
        # The trailer is the STRUCTURAL closer `(try split_ands) <;> assumption` (SMT-free); also accept
        # a bare `euclid_finish` so legacy/hand-wired bodies still recognize as wired.
        ("wired", re.compile(r":=[ \t]*by[ \t\r\n]+euclid_apply[ \t]*\(\s*" + helper +
                             r"\b(?:[^()]|\([^()]*\))*\)[ \t\r\n]*;?[ \t\r\n]*"
                             r"(?:\(try split_ands\)[ \t]*<;>[ \t]*assumption|euclid_finish\b)")),
    ]


def find_body(src, sep_idx, book, name):
    """`sep_idx` is the index of a node's `:=`. Match the canonical body anchored there. Return
    (state, start, end) where state ∈ {sorry,trace,wired} and src[start:end] is the whole body
    (from `:=`). Return None if no canonical shape matches (⟹ not a pipeline node)."""
    for state, rx in _body_regexes(book, name):
        m = rx.match(src, sep_idx)
        if m:
            return state, m.start(), m.end()
    return None


# ── node model ────────────────────────────────────────────────────────────────────────────────────
SENTENCE_HEAD = re.compile(
    r'euclid_sentence\s*"((?:[^"\\]|\\.)*)"\s*"(?:[^"\\]|\\.)*"\s*\(\s*(\w+)\s*:')
HAVE_HEAD = re.compile(r'\bhave\s+(\w+)\s*:')
# A per-node call-args override: `-- @args: a b CF` on its OWN line just above the node head. Supplies
# the EXACT object arguments for this call site's wiring (for a helper reused with DIFFERENT objects per
# parent). Absent ⟹ the wiring defaults to the helper's own binder names. Only the SOURCE of the args
# changes; SP still BUILDS the call, so wrong args fail loudly. The body-swap never touches this line.
ARGS_ANNOT = re.compile(r'(?m)^[ \t]*--[ \t]*@args:[ \t]*(.*?)[ \t]*$')


class Node:
    __slots__ = ("name", "file", "kind", "loc", "claim", "state", "body_start", "body_end", "args")

    def __init__(self, name, file, kind, loc, claim, state, body_start, body_end, args=None):
        self.name, self.file, self.kind = name, file, kind
        self.loc, self.claim, self.state = loc, claim, state
        self.body_start, self.body_end = body_start, body_end   # span of the `:= by …` body in `file`
        self.args = args                                        # [tok,…] from a `-- @args:` line, or None

    def __repr__(self):
        a = f" @args={self.args}" if self.args is not None else ""
        return f"<Node {self.name} ({self.kind}) {os.path.relpath(self.file, BOOK_ROOT)} [{self.state}]{a}>"


def _args_above(src, head_start):
    """If the line IMMEDIATELY above the node head (at index `head_start`) is a `-- @args: …` line,
    return its tokens (a list, possibly empty); else None. Only the line directly above counts, so a
    stray @args comment elsewhere is never silently attached."""
    line_start = src.rfind("\n", 0, head_start) + 1          # start of the head's own line
    if line_start == 0:
        return None
    prev_start = src.rfind("\n", 0, line_start - 1) + 1      # start of the previous line
    prev_line = src[prev_start:line_start - 1]
    m = ARGS_ANNOT.match(prev_line)
    return m.group(1).split() if m else None


def parse_nodes_in_file(path, book):
    """Every goal node in one file: euclid_sentence steps (Main) and canonical `have` nodes (any file).
    A `have` whose body is a REAL proof (not one of the three canonical shapes) is skipped — it is not
    a pipeline node. An euclid_sentence with a non-canonical body is a hard error (Phase A guarantees
    `:= by sorry`)."""
    src = open(path, encoding="utf-8").read()
    nodes = []
    for m in SENTENCE_HEAD.finditer(src):
        loc, name = m.group(1), m.group(2)
        close = balanced_paren(src, m.end())                    # close of the (name : type) annotation
        claim = src[m.end():close]
        am = re.compile(r"\s*:=").match(src, close + 1)
        if not am:
            raise FaithfulError(f"{os.path.relpath(path, BOOK_ROOT)}: euclid_sentence \"{loc}\" has no "
                                f"`:=` body")
        sep = src.index(":=", close + 1)
        body = find_body(src, sep, book, name)
        if not body:
            raise FaithfulError(f"{os.path.relpath(path, BOOK_ROOT)}: euclid_sentence \"{loc}\" "
                                f"({name}) body is not canonical (expected `:= by sorry` or the wired "
                                f"shape). The agent must NEVER hand-write a sentence body.")
        state, bs, be = body
        nodes.append(Node(name, path, "sentence", loc, claim.strip(), state, bs, be,
                          _args_above(src, m.start())))
    for m in HAVE_HEAD.finditer(src):
        name = m.group(1)
        try:
            claim, sep = type_until_assign(src, m.end())
        except FaithfulError:
            continue
        body = find_body(src, sep, book, name)
        if not body:
            continue                                            # a real proof-local `have`, not a node
        state, bs, be = body
        nodes.append(Node(name, path, "have", None, claim.strip(), state, bs, be,
                          _args_above(src, m.start())))
    return nodes


def parse_occurrences(propdir):
    """All node OCCURRENCES across the prop tree, keyed by name → [Node, …]. A `have` reused as a
    shared helper appears (identically) in several containers, so a name maps to ONE-OR-MORE
    occurrences. The naming law still holds: name ≡ ONE backing FILE ≡ helper_<book>_<name> — so the
    same name appearing in two DIFFERENT places is fine (they're the same node, called from each
    parent), and what would be illegal (two different backing files for one name) is caught by
    backing_file(). euclid_sentence step names are unique by construction (one per sentence)."""
    book = book_num(propdir)
    out = {}
    for path in prop_files(propdir):
        for nd in parse_nodes_in_file(path, book):
            out.setdefault(nd.name, []).append(nd)
    # A `have` may recur, but an euclid_sentence STEP must be unique (one realization per sentence).
    for name, occs in out.items():
        sentences = [o for o in occs if o.kind == "sentence"]
        if len(sentences) > 1 or (sentences and len(occs) > 1):
            where = ", ".join(os.path.relpath(o.file, BOOK_ROOT) for o in occs)
            raise FaithfulError(f"node '{name}' is an euclid_sentence step but occurs more than once "
                                f"({where}) — sentence steps must be unique (only `have` helpers may "
                                f"be reused across containers).")
    return out


def parse_all_nodes(propdir):
    """Back-compat: one representative Node per name (the first occurrence). Use for name→backing-file /
    P (once-per-name) work; use parse_occurrences() when you need EVERY call site (SF/SP per parent)."""
    return {name: occs[0] for name, occs in parse_occurrences(propdir).items()}


# ── backing files + object args ─────────────────────────────────────────────────────────────────────
def backing_file(propdir, name):
    """The file `<name>.lean` anywhere in the prop tree, or None."""
    hits = [p for p in prop_files(propdir) if os.path.basename(p) == f"{name}.lean"]
    if len(hits) > 1:
        raise FaithfulError(f"more than one '{name}.lean' in the prop tree: "
                            f"{[os.path.relpath(h, BOOK_ROOT) for h in hits]}")
    return hits[0] if hits else None


def parse_helper_objs(path, book, name):
    """Parse `theorem helper_<book>_<name> (binders…) : claim :=` in its backing file and return
    `(objs, n_hyps)`: the ordered list of OBJECT argument names (binders whose type is a geometric
    sort Point/Line/Circle) and the COUNT of hypothesis (Prop-typed) binders, grouped-binder aware
    (`(h1 h2 : T)` counts 2). The wire fully-applies the helper by passing `objs` positionally and one
    `(by assumption)` per hypothesis binder (see `wired_body`). ABORT LOUD if the theorem is
    missing/misnamed, or a binder's type LOOKS like a sort but isn't a known one (don't guess)."""
    src = open(path, encoding="utf-8").read()
    expected = f"helper_{book}_{name}"
    m = re.search(r"\btheorem\s+(helper_\w+)", src)
    if not m:
        raise FaithfulError(f"{os.path.relpath(path, BOOK_ROOT)}: no `theorem helper_…` found")
    if m.group(1) != expected:
        raise FaithfulError(f"{os.path.relpath(path, BOOK_ROOT)}: theorem is '{m.group(1)}' but the "
                            f"naming law requires '{expected}' (file ↔ node ↔ helper must match)")
    i, n = m.end(), len(src)
    objs, n_hyps = [], 0
    while i < n:
        while i < n and src[i] in " \t\r\n":
            i += 1
        if i >= n:
            break
        if src[i] == ":":            # the result-type separator — binders are done
            break
        if src[i] == "(":
            close = balanced_paren(src, i + 1)
            group = src[i + 1:close]                            # `idents : type`
            ci = group.find(":")
            if ci < 0:
                raise FaithfulError(f"{os.path.relpath(path, BOOK_ROOT)}: malformed binder '({group})'")
            idents, btype = group[:ci].split(), group[ci + 1:].strip()
            if btype in GEOMETRIC_SORTS:
                objs.extend(idents)
            elif re.fullmatch(r"[A-Z]\w*", btype):              # sort-shaped but not a known sort
                raise FaithfulError(f"{os.path.relpath(path, BOOK_ROOT)}: binder '({group})' has "
                                    f"unrecognized sort '{btype}' — known object sorts are "
                                    f"{sorted(GEOMETRIC_SORTS)}. Refusing to guess.")
            else:                                               # a Prop-typed hypothesis binder
                n_hyps += len(idents)
            i = close + 1
        else:
            raise FaithfulError(f"{os.path.relpath(path, BOOK_ROOT)}: unexpected token before the "
                                f"result type of {expected} (only `(binder)` groups are supported)")
    return objs, n_hyps


def wired_body(book, name, objs, n_hyps):
    """The canonical wired body string (single line). The helper is FULLY applied: its object binders
    positionally (`objs`) and one `(by assumption)` per hypothesis binder. Full application makes the
    `euclid_apply` term carry no remaining antecedent arrow, so it takes the no-SMT `obtain` branch
    (SystemE/Meta/Tactics/Solve.lean) — every hypothesis is discharged by core-Lean `assumption`
    (type-match over the local context, including unnamed hyps), NEVER by the SMT solver. A hypothesis
    not present in context makes its `(by assumption)` fail loudly: that signals the helper signature is
    wrong — drop that hyp and derive it inside the helper body.
    The goal is then closed STRUCTURALLY — NOT with `euclid_finish` (which would fall through to the SMT
    solver over the parent's full context and blow the 30s wall even for a trivial leaf). `euclid_apply`
    already `obtain`s the helper's conclusion and `elimAllConjunctions` (Solve.lean:190) recursively
    destructs it into the claim's atoms in context, so `(try split_ands) <;> assumption` closes the goal
    with ZERO SMT: `split_ands` splits a conjunctive claim into conjuncts, each matched by `assumption`
    against a destructed atom (the `try` makes it a no-op for a single-atom claim). The citation is
    recorded by the helper's `euclid_apply` (Solve.lean:166-173, before any branch), so dropping
    `euclid_finish` loses nothing. Net: a leaf wire adds ~0 build time."""
    args = " ".join(objs + ["(by assumption)"] * n_hyps)
    return f":= by euclid_apply ({f'helper_{book}_{name}'} {args}); (try split_ands) <;> assumption"


def resolve_call_args(propdir, book, node):
    """Return `(objs, n_hyps)` for wiring `node`'s call — the OBJECT arguments to pass and the number
    of hypothesis binders (each wired as `(by assumption)`; see `wired_body`). The `@args` override is
    OBJECT-ONLY (hyps are matched by type via `assumption`, never named per call site):
       - if the node carries a `-- @args:` annotation → its tokens VERBATIM as the objects (validated:
         token count == the helper's object-binder count, else FaithfulError — catches arity slips
         before any build). This is how a helper reused with DIFFERENT objects per parent supplies each
         site's actuals.
       - else → the helper's own object-binder names (the default; correct when names already match).
    SP still BUILDS the resulting call, so wrong/misordered/out-of-scope tokens fail loudly there — the
    annotation only changes WHICH objects are passed, never whether the call is accepted."""
    bf = backing_file(propdir, node.name)
    if bf is None:
        raise FaithfulError(f"node '{node.name}' has no backing file '{node.name}.lean'")
    binders, n_hyps = parse_helper_objs(bf, book, node.name)
    if node.args is None:
        return binders, n_hyps
    if len(node.args) != len(binders):
        raise FaithfulError(
            f"node '{node.name}' in {os.path.relpath(node.file, BOOK_ROOT)}: `-- @args:` lists "
            f"{len(node.args)} arg(s) {node.args} but helper_{book}_{node.name} takes {len(binders)} "
            f"object binder(s) {binders}. The override must list EXACTLY the object args, in order.")
    return node.args, n_hyps


# ── the swap primitive (operates on a source STRING; callers handle disk + restore) ─────────────────
def swap_node_body(src, node, new_body_after_assign):
    """Return `src` with `node`'s body (src[node.body_start:node.body_end]) replaced by
    `new_body_after_assign` (a full `:= by …` string). Pure text; the span came from canonical
    matching so this cannot corrupt anything else. Body-only — import is handled by `set_node_state`."""
    return src[:node.body_start] + new_body_after_assign + src[node.body_end:]


def set_node_state(src, node, state, propdir, book):
    """Return `src` with `node` put into `state` ∈ {'sorry','trace','wired'}, managing BOTH the body
    AND the node's helper import together (wiring is body+import; reverting removes both). 'trace' is
    `trace_state; sorry` and, like 'sorry', needs NO helper import; 'wired' adds it.
    The body span is edited FIRST (its indices are valid for the current `src`); the import edit, being
    line-based and idempotent, is applied to the result."""
    if state == "sorry":
        body = ":= by sorry"
    elif state == "trace":
        body = ":= by trace_state; sorry"
    elif state == "wired":
        objs, n_hyps = resolve_call_args(propdir, book, node)
        body = wired_body(book, node.name, objs, n_hyps)
    else:
        raise FaithfulError(f"unknown node state '{state}'")
    out = swap_node_body(src, node, body)
    module = target_of(backing_file(propdir, node.name)) if backing_file(propdir, node.name) else None
    if module:
        out = add_import(out, module) if state == "wired" else remove_import(out, module)
    return out


# ── isolated-SP transforms (wire ONLY this node; sorry the combine tail; signature-only warm) ─────────
def combine_tail_span(src, nodes):
    """Return (tail_start, tail_end): the COMBINE TAIL of a container — the region from the END of the
    LAST node's body to the END of the theorem's `by` block (the namespace `end` / next top-level
    `theorem` / EOF). The tail is the proof work AFTER the last `have` (e.g. `linarith [...]`, or Main's
    `exact step28; euclid_conclude_sentence …`). Returns None if `nodes` is empty (a pure leaf — no
    tail). Invariant: ONE `theorem helper_…` per backing file (enforced by parse_helper_objs); Main has
    one theorem too. Uses a comment-blanked copy so a commented `end`/`theorem` is ignored."""
    if not nodes:
        return None
    tail_start = max(nd.body_end for nd in nodes)
    clean = blank_comments(src)
    end = None
    for m in re.finditer(r"^(?:end|theorem)\b", clean, re.MULTILINE):
        if m.start() >= tail_start:
            end = m.start()
            break
    tail_end = end if end is not None else len(src)
    return (tail_start, tail_end)


def set_theorem_body_sorry(src):
    """Return `src` with the file's single top-level theorem body replaced by `:= by sorry` — a
    SIGNATURE-ONLY form (proof-irrelevant: the exported `helper_… : ∀ objs, hyps → claim` type is
    unchanged). Used to warm a backing-file olean WITHOUT building its real proof, so an isolated-SP
    build never depends on the node's body. Scans from the theorem's first top-level `:=` to the
    namespace `end`/EOF (comment-blanked) and swaps that whole proof region for ` := by sorry`."""
    m = re.search(r"^theorem\s", src, re.MULTILINE)
    if not m:
        raise FaithfulError("set_theorem_body_sorry: no top-level `theorem`")
    # find the theorem's top-level `:=` (the proof separator), respecting brackets/strings
    depth, i, n = 0, m.end(), len(src)
    assign = None
    while i < n:
        c = src[i]
        if c == '"':
            i = _skip_string(src, i, n); continue
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif depth == 0 and src.startswith(":=", i):
            assign = i; break
        i += 1
    if assign is None:
        raise FaithfulError("set_theorem_body_sorry: no top-level `:=` for the theorem")
    clean = blank_comments(src)
    em = re.search(r"^end\b", clean[assign:], re.MULTILINE)
    body_end = assign + em.start() if em else len(src)
    return src[:assign] + ":= by sorry\n\n" + src[body_end:]


def set_node_isolated_sp(src, node, nodes, propdir, book):
    """Return `src` transformed for an ISOLATED SP build of `node` in its container:
      - the COMBINE TAIL (everything after the last node's body) → `sorry`, so the combine NEVER runs;
      - `node` → WIRED (its `(by assumption)` call + helper import);
      - ALL OTHER nodes: untouched (they are already dev `:= by sorry`, contributing only their claim
        TYPES as context — that IS the parent's supply).
    Edits are applied HIGHEST-offset first so earlier spans stay valid. `nodes` = parse_nodes_in_file of
    the container. The result wires exactly ONE node ⟹ SP is O(1) and exercises only THIS node's wire."""
    out = src
    tail = combine_tail_span(src, nodes)
    # tail edit first (it is at the highest offset — after every node body)
    if tail is not None:
        ts, te = tail
        # only truncate if the tail is AFTER this node (it always is: tail_start = last node's body_end)
        out = out[:ts] + "\n  sorry\n" + out[te:]
    # then wire THIS node (its body_start/body_end are < ts, so unaffected by the tail edit)
    out = set_node_state(out, node, "wired", propdir, book)
    return out


# ── caps ────────────────────────────────────────────────────────────────────────────────────────────
def strip_caps(src):
    """Remove every `set_option systemE.solverTime N in` line (whole line). For Phase C."""
    return CAP_RE.sub("", src)


def add_cap(src):
    """Insert the canonical 30s cap line immediately above the file's theorem, if not already capped.
    For Phase-C --unwire (restore the dev state)."""
    if CAP_RE.search(src):
        return src
    m = re.search(r"^theorem\s", src, re.MULTILINE)
    if not m:
        raise FaithfulError("no top-level `theorem` to cap")
    return src[:m.start()] + CAP_LINE + "\n" + src[m.start():]


# ── helper-import management (the OTHER half of wiring — script-owned, transient) ────────────────────
# Wiring a node = body swap + an `import <backing-module>` so `helper_<book>_<name>` resolves. In the
# dev/sorry state a container imports NONE of its pipeline backing files; the script adds the import
# when it wires a node and removes it when it reverts. The LLM never writes a helper/step import.
def prop_prefix(propdir):
    """The Lean module prefix of a prop's own files, e.g. `Book2.Prop04`. Used to detect/strip the
    pipeline (helper/step) imports — those under the prop's OWN prefix — vs. legitimate SystemE /
    cited-proposition imports (which are LLM-written proof content and are left alone)."""
    return os.path.relpath(os.path.realpath(propdir), BOOK_ROOT).replace(os.sep, ".")


def _import_re(module):
    return re.compile(r"^[ \t]*import[ \t]+" + re.escape(module) + r"[ \t]*\r?\n", re.MULTILINE)


def has_import(src, module):
    return _import_re(module).search(src) is not None


def add_import(src, module):
    """Insert `import <module>` if absent, on its own line, right after the LAST existing `import` line
    (imports must precede any declaration in Lean). Idempotent."""
    if has_import(src, module):
        return src
    last = None
    for m in re.finditer(r"^[ \t]*import[ \t]+\S+[ \t]*\r?\n", src, re.MULTILINE):
        last = m
    line = f"import {module}\n"
    if last:
        return src[:last.end()] + line + src[last.end():]
    return line + src                                   # no imports yet (unusual) — prepend


def remove_import(src, module):
    """Remove an `import <module>` line if present. Idempotent."""
    return _import_re(module).sub("", src)


def pipeline_imports(src, propdir):
    """Every import in `src` that targets a file UNDER this prop's own prefix (i.e. a helper/step
    import). In a clean dev state this list is empty; --check flags any as 'stray helper imports'."""
    pre = prop_prefix(propdir)
    return [m.group(1) for m in re.finditer(r"^[ \t]*import[ \t]+(\S+)", src, re.MULTILINE)
            if m.group(1) == pre or m.group(1).startswith(pre + ".")]


# ── build under flock + optional wall timeout (replicates safe_build.sh's two jobs) ──────────────────
def _clean_output(out):
    """Drop lake's giant `trace: .> LEAN_PATH=… lean … --json` command-echo line (it can be 4 000+
    chars of dynlib flags and otherwise swamps the actual error/goal lines callers tail)."""
    if not out:
        return out
    keep = [ln for ln in out.splitlines()
            if not (ln.lstrip().startswith("trace: .>") or "LEAN_PATH=" in ln)]
    return "\n".join(keep)


def warm_build(target):
    """Build `target` with NO wall timeout, just to populate its .olean (so a later WALLED build that
    imports it measures only its own work, not this dependency's compile). Returns (ok, output)."""
    return lake_build(target, wall=None)


# INFRA-FLAKE signature: the smt-portfolio python (miniforge/conda on a networked FS) intermittently
# fails to LOAD AT STARTUP — `failed to map segment from shared object` / an ImportError on a stdlib
# `.so`. This is NOT a proof result (z3/cvc5 never ran) and NOT a timeout; it's a launch hiccup. We
# RETRY the build a few times on this signature only — never on a real error (wrong proof) or a wall
# timeout (a genuine TOO-BIG verdict), so retrying can never mask a real failure.
FLAKE_RE = re.compile(r"failed to map segment from shared object|"
                      r"ImportError:.*\.so|cannot? (?:open|load) shared object|Error relocating", re.I)
FLAKE_RETRIES = 3


def _lake_build_once(target, wall, env, lock_handlers_proc):
    """One `lake build <target>` attempt. Returns (ok, output, timed_out)."""
    proc = subprocess.Popen(["lake", "build", target], cwd=BOOK_ROOT, env=env,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            text=True, start_new_session=True)
    lock_handlers_proc[0] = proc                       # expose for the signal handler / killpg
    try:
        out, _ = proc.communicate(timeout=wall)
        return proc.returncode == 0, _clean_output(out), False
    except subprocess.TimeoutExpired:
        if proc.poll() is None:
            try:
                os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
            except ProcessLookupError:
                pass
        partial, _ = proc.communicate()
        return False, _clean_output(partial or ""), True


def lake_build(target, wall=WALL):
    """Run `lake build <target>` with the venv bin on PATH (z3/cvc5) and an exclusive flock on
    .lake/build.lock (parallel-agent safe). If `wall` is not None, kill the whole process group at
    `wall` seconds. Auto-RETRIES (same target, deps stay cached) on the INFRA-FLAKE signature only —
    never on a real error or a timeout. Return (ok: bool, output: str). The agent never types
    `lake`/`timeout` directly — this owns it, prompt-free."""
    env = dict(os.environ)
    venv_bin = os.path.join(os.environ.get("LEANEUCLID_VENV", DEFAULT_VENV), "bin")
    if os.path.isdir(venv_bin):
        env["PATH"] = venv_bin + os.pathsep + env.get("PATH", "")
    lock_path = os.path.join(BOOK_ROOT, ".lake", "build.lock")
    os.makedirs(os.path.dirname(lock_path), exist_ok=True)
    with open(lock_path, "w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        box = [None]                                   # box[0] = current Popen, for the signal handler

        # The child runs in its OWN session (needed for clean timeout-kill), so a terminal Ctrl-C does
        # NOT reach it. Install handlers that kill the current child's process group, then re-raise — so
        # Ctrl-C doesn't leave an orphaned `lake` holding the build lock.
        prev = {}

        def _handler(signum, frame):
            p = box[0]
            if p and p.poll() is None:
                try:
                    os.killpg(os.getpgid(p.pid), signal.SIGKILL)
                except ProcessLookupError:
                    pass
            signal.signal(signum, prev.get(signum, signal.SIG_DFL))
            os.kill(os.getpid(), signum)

        for sig in (signal.SIGINT, signal.SIGTERM):
            prev[sig] = signal.getsignal(sig)
            signal.signal(sig, _handler)
        try:
            for attempt in range(1, FLAKE_RETRIES + 1):
                ok, out, timed_out = _lake_build_once(target, wall, env, box)
                if timed_out:
                    tail = "\n".join((out or "").rstrip().splitlines()[-25:])
                    msg = (f"[faithful_lib] build of {target} exceeded {wall}s wall clock — TOO BIG. "
                           f"DECOMPOSE into more backing files; NEVER raise the cap. Last output before "
                           f"the kill (what it was elaborating when it stalled):")
                    return False, (msg + "\n" + tail if tail.strip() else msg)
                if not ok and FLAKE_RE.search(out or "") and attempt < FLAKE_RETRIES:
                    print(f"[faithful_lib] {target}: SMT-portfolio launch flake (not a proof failure) — "
                          f"retrying build (attempt {attempt + 1}/{FLAKE_RETRIES})…", flush=True)
                    continue
                return ok, out
            return ok, out                             # exhausted retries: report the last (flaky) output
        finally:
            for sig, h in prev.items():
                signal.signal(sig, h)
            fcntl.flock(lock, fcntl.LOCK_UN)


def has_sorry(output):
    """True iff a build emitted a `declaration uses 'sorry'` warning (a 'green' build with sorry is NOT
    proven)."""
    return "declaration uses 'sorry'" in output


# ── atomic restore guard ────────────────────────────────────────────────────────────────────────────
class restore_files:
    """Context manager: snapshot the exact bytes of `paths`, and restore them on __exit__ (success OR
    exception) AND on SIGINT/SIGTERM. Guarantees a killed/timed-out swap never leaves a file wired or
    trace_state'd — the real Main/step files always end byte-identical to how they started."""
    def __init__(self, paths):
        self.snap = {p: open(p, "rb").read() for p in paths}
        self._prev = {}

    def restore(self):
        for p, b in self.snap.items():
            with open(p, "wb") as f:
                f.write(b)

    def _handler(self, signum, frame):
        self.restore()
        signal.signal(signum, self._prev.get(signum, signal.SIG_DFL))
        os.kill(os.getpid(), signum)

    def __enter__(self):
        for sig in (signal.SIGINT, signal.SIGTERM):
            self._prev[sig] = signal.getsignal(sig)
            signal.signal(sig, self._handler)
        return self

    def __exit__(self, *exc):
        self.restore()
        for sig, h in self._prev.items():
            signal.signal(sig, h)
        return False


# ── shared structural pre-check (used by --check and as the abort-loud preamble of build ops) ────────
def integrity_scan(propdir):
    """Source-only, NO builds. Verify the naming law and dev-state invariants. Returns a list of
    human-readable problem strings (empty ⟹ structurally sound). Raises FaithfulError only on a parse
    failure so malformed source is never silently accepted."""
    book = book_num(propdir)
    problems = []
    occ = parse_occurrences(propdir)
    for name, occs in sorted(occ.items()):
        bf = backing_file(propdir, name)
        if bf is None:
            problems.append(f"node '{name}' ({os.path.relpath(occs[0].file, BOOK_ROOT)}) has NO backing "
                            f"file '{name}.lean' — every sorry node must have one (the naming law).")
            continue
        try:
            parse_helper_objs(bf, book, name)                   # validates theorem name == helper_<book>_<name>
        except FaithfulError as e:
            problems.append(str(e))
        for nd in occs:                                          # check EVERY call site, not just one
            if nd.state == "wired":
                problems.append(f"node '{name}' is already WIRED on disk in "
                                f"{os.path.relpath(nd.file, BOOK_ROOT)} — the dev state must be "
                                f"`:= by sorry` (only Phase C wires; check_step never leaves wiring).")
            if nd.args is not None:                              # validate `-- @args:` token count
                try:
                    resolve_call_args(propdir, book, nd)
                except FaithfulError as e:
                    problems.append(str(e))
    # every file in the dev state should carry the EXACT 30s cap, and import NO pipeline file
    for path in prop_files(propdir):
        src = open(path, encoding="utf-8").read()
        if not CAP_RE_EXACT.search(src):
            if CAP_RE.search(src):
                problems.append(f"{os.path.relpath(path, BOOK_ROOT)} has a `solverTime` cap that is NOT "
                                f"the required `{CAP_LINE}` — the dev cap is exactly {CAP_SECONDS}s; "
                                f"don't raise it (decompose instead).")
            else:
                problems.append(f"{os.path.relpath(path, BOOK_ROOT)} is missing "
                                f"`{CAP_LINE}` above its theorem.")
        for mod in pipeline_imports(src, propdir):
            problems.append(f"{os.path.relpath(path, BOOK_ROOT)} has a STRAY helper import "
                            f"`import {mod}` — only the script may add pipeline imports (transiently "
                            f"when wiring). Remove it; the dev state imports no helper/step file.")
        # ORPHAN `-- @args:` guard: every @args line must sit DIRECTLY above a node head (`have <n> :`
        # or `euclid_sentence …`); otherwise it's silently ignored (e.g. a blank line crept between).
        # Flag it loudly so the override never silently no-ops.
        for m in ARGS_ANNOT.finditer(src):
            nl = src.find("\n", m.end())
            nxt = src[nl + 1:] if nl != -1 else ""
            if not (re.match(r'[ \t]*have\s+\w+\s*:', nxt) or
                    re.match(r'[ \t]*euclid_sentence\b', nxt)):
                ln = src.count("\n", 0, m.start()) + 1
                problems.append(f"{os.path.relpath(path, BOOK_ROOT)}:{ln} has a `-- @args:` line that "
                                f"is NOT directly above a node head (`have …`/`euclid_sentence …`) — it "
                                f"would be silently ignored. Put it on the line immediately above the "
                                f"node, or remove it.")
        # NO STRAY `sorry` / cheat token. The ONLY sorries allowed are declared NODE bodies (`:= by
        # sorry`, which become wired). A `sorry`/`admit`/`native_decide`/`axiom` ANYWHERE ELSE — e.g. a
        # faked container combine written `… := by sorry` as a bare tactic, or a leaf that cheats — is a
        # hard error. This is what lets P be LEAF-ONLY and `--all` still GUARANTEE Phase C: SP doesn't
        # catch a stray sorry (a build with a sorry warning still "succeeds"), so the guarantee depends
        # on this source scan. Node bodies (their canonical `:= by sorry` spans) are the only exemption.
        clean = blank_comments(src)
        node_body_spans = [(nd.body_start, nd.body_end) for nd in parse_nodes_in_file(path, book)]
        for cm in CHEAT_RE.finditer(clean):
            pos = cm.start()
            if any(s <= pos < e for s, e in node_body_spans):
                continue                                        # a declared node's own `:= by sorry` — fine
            ln = clean.count("\n", 0, pos) + 1
            problems.append(f"{os.path.relpath(path, BOOK_ROOT)}:{ln} has a STRAY `{cm.group(0).strip()}` "
                            f"that is NOT a declared node body — proofs may not be faked. (A container's "
                            f"combine must be real tactics, e.g. `euclid_finish`, never `sorry`; only a "
                            f"node's canonical `:= by sorry` is allowed, and only because the script wires it.)")
    return problems
