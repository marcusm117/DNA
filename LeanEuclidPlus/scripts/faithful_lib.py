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
import os, re, sys, glob, signal, subprocess, fcntl, hashlib, json

# ── locations / constants ─────────────────────────────────────────────────────────────────────────
# realpath (not just abspath): the repo is reachable via both /h/56/taddmao/… and /u/taddmao/… (a
# symlink). If BOOK_ROOT and an incoming path resolve through different roots, os.path.relpath yields a
# garbage `../../../u/…` Lean target. Canonicalizing both ends here makes every relpath/target_of sound.
BOOK_ROOT = os.path.realpath(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))   # LeanEuclidPlus/
DEFAULT_VENV = os.path.expanduser("~/.venvs/leaneuclid")
GEOMETRIC_SORTS = {"Point", "Line", "Circle"}      # the only `axiom … : Type` object sorts (Sorts/Primitives.lean)
CAP_LINE = "set_option systemE.solverTime 30 in"
CAP_SECONDS = 30                                    # the ONE allowed dev SMT cap (solverTime, enforced by --check)
# CAP_RE matches ANY solverTime line (used to strip/detect a cap regardless of value).
CAP_RE   = re.compile(r"^[ \t]*set_option[ \t]+systemE\.solverTime[ \t]+\d+[ \t]+in[ \t]*\r?\n", re.MULTILINE)
# CAP_RE_EXACT matches ONLY the canonical 30s cap — `--check` requires this exact value so a bumped
# `solverTime 300` is flagged (the wall still kills it, but the structural guard should catch it too).
CAP_RE_EXACT = re.compile(r"^[ \t]*set_option[ \t]+systemE\.solverTime[ \t]+" + str(CAP_SECONDS) +
                          r"[ \t]+in[ \t]*\r?\n", re.MULTILINE)
# The per-build wall timeout (dev only). DELIBERATELY > CAP_SECONDS: the SMT cap (30s) is the proving
# BUDGET (a build whose solver gives up at 30s is still "too big → decompose"); the wall is only a
# diagnostic/safety bound. Decoupling them (45 > 30) gives the slow-`euclid_finish` case ~15s of headroom
# to emit Lean's LOCATED "Could not prove" error (path the agent can act on: which line/`have` failed)
# BEFORE the wall SIGKILLs the process (which yields only an unlocated stdout tail). It also stops non-SMT
# elaboration/translation overhead from eating into the usable 30s SMT budget. A wall-kill now means a
# genuine >45s hang, still "decompose". Wall time is free per the cost model, so this costs nothing.
WALL = 45

# Phase-C linter suppression: the WIRED build's machine-generated form trips two cosmetic linters that
# are simply the wrong lint for generated faithful proofs — (1) `unusedVariables`: a helper signature
# declares EVERY context-suppliable hypothesis (so the zero-SMT wire can discharge it), but a given proof
# body need not reference all of them; (2) `unnecessarySeqFocus`: the uniform closer `(try split_ands)
# <;> assumption` uses `<;>`, which the linter flags as unnecessary on single-atom (non-conjunctive)
# claims. Neither indicates a defect. wire_main prepends these `set_option … false` lines on WIRE and
# strips them on --unwire (mirroring caps), so ONLY the committed wired files are silenced — hand-written
# code and dev-state builds keep both lints.
LINTER_LINES = ("set_option linter.unusedVariables false\n"
                "set_option linter.unnecessarySeqFocus false\n")
LINTER_RE = re.compile(r"^[ \t]*set_option[ \t]+linter\.(?:unusedVariables|unnecessarySeqFocus)[ \t]+"
                       r"(?:true|false)[ \t]*\r?\n", re.MULTILINE)


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
    """`…/Book2/Prop04` → 2.  The <book> in helper_<book>_<prop>_<name>."""
    for part in os.path.relpath(propdir, BOOK_ROOT).split(os.sep):
        m = re.fullmatch(r"Book(\d+)", part)
        if m:
            return int(m.group(1))
    raise FaithfulError(f"cannot determine book number from {os.path.relpath(propdir, BOOK_ROOT)}")


def prop_num(path):
    """`…/Book2/Prop04` or `…/Book2/Prop04/step5.lean` → 4.  The <prop> in helper_<book>_<prop>_<name>.
    Works on a propdir OR any file path under it (a `Prop<NN>` segment must be present). The prop number
    in the helper name is what makes `helper_2_2_step1` (Prop02) and `helper_2_3_step1` (Prop03) distinct
    constants, so the whole book builds without an `environment already contains` collision."""
    for part in os.path.relpath(os.path.realpath(path), BOOK_ROOT).split(os.sep):
        m = re.fullmatch(r"Prop(\d+)", part)
        if m:
            return int(m.group(1))
    raise FaithfulError(f"cannot determine prop number from {os.path.relpath(path, BOOK_ROOT)}")


def helper_name(book, prop, name):
    """The canonical helper theorem name: `helper_<book>_<prop>_<name>` (the ONE place it's built)."""
    return f"helper_{book}_{prop}_{name}"


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


# ── declaration fact extraction (bake_index / find support — PURE PARSE, no Lean) ─────────────────────
# A small, CLOSED registry of System-E's geometric vocabulary, transcribed ONCE from
# SystemE/Theory/Relations.lean + the Sorts/ notations. `bake_index.py` turns each declaration's
# hypotheses/conclusion into a list of {symbol, role, polarity} "facts" so `find.py` can answer
# "what CONCLUDES X / CONSUMES X / MENTIONS X" off one parse. The registry is the only place the
# vocabulary lives; adding a relation here is all a new symbol needs.

# Opaque relation predicates (Relations.lean). Keyed by METHOD name as it appears in USE position
# (lowercase-initial dot-form `a.onLine`, bare `between a b c`, or `Point.onLine`). The method name is
# matched with a word boundary; because the abbrev `distinctPointsOnLine` spells it `…OnLine` (capital
# O), `\bonLine\b` matches `a.onLine` but never the abbrev — no lookbehind needed.
OPAQUE_METHODS = ("onLine", "sameSide", "collinear", "between", "onCircle", "insideCircle",
                  "isCentre", "intersectsLine", "intersectsCircle")

# `@[simp] abbrev`s (Relations.lean). Each maps to its UNFOLDED atomic facts as (symbol, polarity)
# pairs — pre-flattened by hand (the set is closed + acyclic, so no runtime recursion). A positive
# abbrev occurrence emits BOTH the packaged fact (its own name) AND these unfolded atoms (tagged
# `via=<abbrev>`), so a query for `onLine` finds a prop that only mentions it inside `formTriangle`,
# and a future first-order matcher sees atom-level hyps. A NEGATED abbrev emits the packaged fact only
# (De Morgan over the body is intentionally not attempted — no corpus case negates a whole abbrev).
ABBREV_UNFOLD = {
    "distinctPointsOnLine": [("onLine", "pos"), ("onLine", "pos"), ("ne", "neg")],
    "opposingSides":        [("onLine", "neg"), ("onLine", "neg"), ("sameSide", "neg")],
    "outsideCircle":        [("insideCircle", "neg"), ("onCircle", "neg")],
    "formTriangle":         [("onLine", "pos"), ("onLine", "pos"), ("ne", "neg"),
                             ("onLine", "pos"), ("onLine", "pos"), ("onLine", "pos"), ("onLine", "pos"),
                             ("ne", "neg"), ("ne", "neg"), ("ne", "neg")],
    "formRectilinearAngle": [("onLine", "pos"), ("onLine", "pos"), ("ne", "neg"),
                             ("onLine", "pos"), ("onLine", "pos"), ("ne", "neg")],
    "formParallelogram":    [("onLine", "pos"), ("onLine", "pos"), ("onLine", "pos"), ("onLine", "pos"),
                             ("onLine", "pos"), ("onLine", "pos"),
                             ("onLine", "pos"), ("onLine", "pos"), ("ne", "neg"),  # distinctPointsOnLine b d BD
                             ("sameSide", "pos"), ("intersectsLine", "neg"), ("intersectsLine", "neg")],
}

# Metric notations (Sorts/{Segments,Angles,Triangles}.lean) → symbol. Detected by their distinctive
# unicode glyph (or the underlying `Namespace.method`).
_METRIC_TOKENS = (
    ("right_angle", re.compile(r"∟|\bAngle\.Right\b")),       # check BEFORE angle so ∟ isn't 'angle'
    ("angle",       re.compile(r"∠|\bAngle\.degree\b")),
    ("area",        re.compile(r"△|\bTriangle\.area\b")),
    ("length",      re.compile(r"─|\bSegment\.length\b|\|[^|]+\|")),
)
# Top-level comparators → symbol. `≠` is recorded as `ne` with polarity neg (the doc's "≠ = ¬=");
# the others inherit the conjunct's polarity. Single-glyph unicode (≠ ≤ ≥) and ascii (= < >).
_COMPARATORS = {"≠": "ne", "=": "eq", "<": "lt", ">": "gt", "≤": "le", "≥": "ge"}

# Sort-typed binders are OBJECTS (counted in object_arity); everything else is a hypothesis binder.
SORT_TYPES = {"Point", "Line", "Circle", "Segment", "Triangle", "Angle", "ℝ", "Real", "ℕ", "Nat"}

# The CLOSED set of canonical fact symbols a query (`find.py --concludes/--consumes/--mentions`) may
# name — derived from the registry above so there is ONE source of truth. Every value that
# `extract_facts` can emit appears here.
VALID_SYMBOLS = (set(OPAQUE_METHODS) | set(ABBREV_UNFOLD)
                 | {sym for sym, _ in _METRIC_TOKENS} | set(_COMPARATORS.values()))

# Source-form → canonical-symbol aliases, so a query may use the form you'd copy from a `.lean` file
# (`Triangle.area`, `∟`, `Line.intersectsLine`, `=`) instead of the bare canonical name. Built from the
# same registry. `canon_symbol()` applies these; an input already canonical passes through unchanged.
SYMBOL_ALIASES = {
    # metric notations + their underlying methods
    "△": "area", "Triangle.area": "area", "area": "area",
    "∠": "angle", "Angle.degree": "angle", "angle": "angle",
    "∟": "right_angle", "Angle.Right": "right_angle", "right-angle": "right_angle",
    "rightangle": "right_angle", "right_angle": "right_angle",
    "─": "length", "Segment.length": "length", "length": "length", "len": "length",
    # comparators in punctuation form
    "=": "eq", "≠": "ne", "!=": "ne", "<": "lt", ">": "gt",
    "≤": "le", "<=": "le", "≥": "ge", ">=": "ge",
}
# every opaque method also reachable via its dotted receiver forms (`a.onLine`, `Point.onLine`)
for _m in OPAQUE_METHODS:
    SYMBOL_ALIASES[_m] = _m
    for _ns in ("Point", "Line", "Circle"):
        SYMBOL_ALIASES[f"{_ns}.{_m}"] = _m
for _ab in ABBREV_UNFOLD:                              # abbrevs are their own canonical names
    SYMBOL_ALIASES[_ab] = _ab


def canon_symbol(token):
    """Map a user-typed symbol to its canonical form, accepting source notations (`Triangle.area`→`area`,
    `∟`→`right_angle`, `a.onLine`/`Point.onLine`→`onLine`, `=`→`eq`, …). A leading `*.` receiver
    (`b.sameSide`) is stripped to the method. Returns the canonical symbol if recognized, else the
    (stripped) token unchanged — the caller validates against VALID_SYMBOLS and reports if unknown."""
    t = token.strip()
    if t in SYMBOL_ALIASES:
        return SYMBOL_ALIASES[t]
    if t in VALID_SYMBOLS:
        return t
    if "." in t:                                       # e.g. `b.sameSide`, `α.onCircle` → method tail
        tail = t.rsplit(".", 1)[-1]
        if tail in SYMBOL_ALIASES:
            return SYMBOL_ALIASES[tail]
        if tail in VALID_SYMBOLS:
            return tail
    return t


def _strip_outer_parens(s):
    """If `s` is wholly wrapped in one balanced `(…)`, return the inside; else `s` unchanged."""
    s = s.strip()
    if s.startswith("(") and s.endswith(")"):
        try:
            if balanced_paren(s, 1) == len(s) - 1:
                return s[1:-1].strip()
        except FaithfulError:
            pass
    return s


def _split_top_level(text, seps):
    """Split `text` on any separator string in `seps` that occurs at bracket/paren depth 0 (and not
    inside a string literal). `seps` are matched greedily-longest-first at each position. Returns the
    list of pieces (separators removed)."""
    parts, buf, i, n, depth = [], [], 0, len(text), 0
    seps = sorted(seps, key=len, reverse=True)
    while i < n:
        c = text[i]
        if c == '"':
            j = _skip_string(text, i, n)
            buf.append(text[i:j]); i = j; continue
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        if depth == 0:
            hit = next((s for s in seps if text.startswith(s, i)), None)
            if hit:
                parts.append("".join(buf)); buf = []; i += len(hit); continue
        buf.append(c); i += 1
    parts.append("".join(buf))
    return parts


def parse_binders(text):
    """Parse a run of Lean binder groups (`(a b : Point) (h : P) {x : T} [inst]`) into a list of
    `(idents, type)` pairs (one per group; `idents` is a list, `type` the stripped type text). LENIENT:
    unlike `parse_helper_objs` it never raises on an unfamiliar sort — it just records the type so the
    caller (bake_index) can classify object-vs-hypothesis. Instance binders `[…]` yield `([], type)`."""
    out, i, n = [], 0, len(text)
    while i < n:
        while i < n and text[i] in " \t\r\n":
            i += 1
        if i >= n:
            break
        if text[i] in "([{":
            close = balanced_paren(text, i + 1) if text[i] == "(" else _matching(text, i)
            group = text[i + 1:close]
            ci = group.find(":")
            if ci < 0:                                   # e.g. an autobound `{α}` or `[inst]` w/o `:`
                out.append(([] if text[i] == "[" else group.split(), ""))
            else:
                out.append((group[:ci].split(), group[ci + 1:].strip()))
            i = close + 1
        else:                                            # not a binder group — stop (defensive)
            break
    return out


def _matching(src, start):
    """Index of the bracket matching the `{`/`[`/`(` at `src[start]` (paren/string aware)."""
    depth, i, n = 0, start, len(src)
    pairs = {"(": ")", "[": "]", "{": "}"}
    while i < n:
        c = src[i]
        if c == '"':
            i = _skip_string(src, i, n); continue
        if c in pairs:
            depth += 1
        elif c in pairs.values():
            depth -= 1
            if depth == 0:
                return i
        i += 1
    raise FaithfulError("unbalanced bracket while scanning")


def split_signature(header):
    """Split a declaration's header (everything between the decl NAME and its `:=`/end-of-axiom) into
    `(binders_text, type_text)`. The result type begins at the FIRST top-level `:` (the one that is NOT
    inside a binder group and NOT the `:=` proof separator); everything before it is the leading
    (curried) binders, everything after is the type. For a `∀`-style prop (`theorem p : ∀ …`) the
    binders_text is empty and type_text is the whole `∀ …`."""
    i, n, depth = 0, len(header), 0
    while i < n:
        c = header[i]
        if c == '"':
            i = _skip_string(header, i, n); continue
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        elif depth == 0 and c == ":" and not header.startswith(":=", i):
            return header[:i].strip(), header[i + 1:].strip()
        i += 1
    return header.strip(), ""                            # no result `:` (defensive) — all binders


def split_quantifier_and_arrow(type_text):
    """Decompose a type `∀ (binders), H₁ ∧ … → C` into `(binders_text, hyps_text, concl_text,
    concludes_exists)`. Peels a leading `∀ …,` (binders), splits the remainder on top-level `→` (all
    but the last segment are hypotheses; the last is the conclusion), then strips a leading `∃`/`exists`
    quantifier off the conclusion (constructions conclude existentially), setting `concludes_exists`."""
    t = type_text.strip()
    binders = ""
    m = re.match(r"(?:∀|\bforall\b)\s*", t)
    if m:
        rest = t[m.end():]
        segs = _split_top_level(rest, [","])
        binders = segs[0].strip()
        t = ",".join(segs[1:]).strip() if len(segs) > 1 else ""
    arrow_segs = _split_top_level(t, ["→"])
    if len(arrow_segs) >= 2:
        hyps = " ∧ ".join(s.strip() for s in arrow_segs[:-1])
        concl = arrow_segs[-1].strip()
    else:
        hyps, concl = "", t.strip()
    concludes_exists = False
    em = re.match(r"(?:∃|\bexists\b)\s*", concl)
    if em:
        body_segs = _split_top_level(concl[em.end():], [","])
        if len(body_segs) > 1:                           # strip `∃ vars,`
            concl = ",".join(body_segs[1:]).strip()
            concludes_exists = True
    return binders, hyps, concl, concludes_exists


def split_conjuncts(region):
    """Split a hypothesis/conclusion region into atomic conjuncts on top-level `∧` (and `∨`, so a
    disjunctive conclusion's branches are each recorded). Outer parens are peeled first. Empty pieces
    are dropped."""
    region = _strip_outer_parens(region.strip())
    if not region:
        return []
    return [p.strip() for p in _split_top_level(region, ["∧", "∨"]) if p.strip()]


def _fact(symbol, role, polarity, raw, via=None):
    return {"symbol": symbol, "role": role, "polarity": polarity, "raw": raw, "via": via}


def _conjunct_facts(conj, role):
    """Every fact in one atomic conjunct: its abbrev (packaged + unfolded), opaque-predicate, metric,
    and comparator symbols, each with role + polarity. A leading `¬` flips polarity to neg; a top-level
    `≠` always emits `ne`/neg."""
    raw = conj.strip()
    inner = _strip_outer_parens(raw)
    nm = re.match(r"¬\s*", inner)
    neg = bool(nm)
    if nm:
        inner = _strip_outer_parens(inner[nm.end():])
    pol = "neg" if neg else "pos"
    facts, seen = [], set()

    def add(sym, polarity, via=None):
        key = (sym, polarity, via)
        if key not in seen:
            seen.add(key)
            facts.append(_fact(sym, role, polarity, raw, via))

    for ab, atoms in ABBREV_UNFOLD.items():
        if re.search(r"\b" + ab + r"\b", inner):
            add(ab, pol)
            if not neg:                                  # unfold positive abbrevs only
                for sym, apol in atoms:
                    add(sym, apol, via=ab)
    for meth in OPAQUE_METHODS:
        if re.search(r"\b" + meth + r"\b", inner):
            add(meth, pol)
    for sym, rx in _METRIC_TOKENS:
        if rx.search(inner):
            add(sym, pol)
    for glyph, sym in _comparators_at_top(inner):
        add(sym, "neg" if glyph == "≠" else pol)
    return facts


def _comparators_at_top(text):
    """Yield (glyph, symbol) for each comparator at bracket depth 0 (deduped). Skips the `:=`/`==`
    cases (types contain neither, but be safe)."""
    out, i, n, depth, seen = [], 0, len(text), 0, set()
    while i < n:
        c = text[i]
        if c == '"':
            i = _skip_string(text, i, n); continue
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        elif depth == 0 and c in _COMPARATORS:
            if c == "=" and (text[i - 1:i] == ":" or text[i + 1:i + 1] == "="):
                i += 1; continue
            if c not in seen:
                seen.add(c); out.append((c, _COMPARATORS[c]))
        i += 1
    return out


def extract_facts(region, role):
    """All facts in a hypothesis or conclusion region (`role` ∈ {'hyp','concl'}): split into conjuncts,
    extract each conjunct's symbols. See `_conjunct_facts`."""
    out = []
    for conj in split_conjuncts(region):
        out.extend(_conjunct_facts(conj, role))
    return out


# Capture the FULL dotted head of an `euclid_apply (HEAD …)` call — HEAD may be namespace-qualified
# (`Elements.Book1.proposition_46`) or bare (`proposition_31`, `line_from_points`, `helper_2_4_step1`).
_APPLY_HEAD_RE = re.compile(r"euclid_apply\s*\(\s*([A-Za-z_][\w'.]*)")


def cited_in_body(body_text):
    """The ordered, de-duplicated list of DECLARATION NAMES cited by `euclid_apply (NAME …)` in a proof
    body — propositions (`proposition_30`), constructions (`line_from_points`), and helpers (`helper_…`).
    The head of each call is parsed off a comment-blanked copy (so a commented call is ignored), and any
    namespace qualifier is STRIPPED to the final component, so a call written `Elements.Book1.proposition_46`
    records `proposition_46` — identical to the bare form, so `--cites proposition_46` matches both. (The
    cited decl's own book/prop is a property of ITS row: look it up with `find.py --name <decl>`.)"""
    out, seen = [], set()
    for m in _APPLY_HEAD_RE.finditer(blank_comments(body_text)):
        name = m.group(1).rstrip(".").split(".")[-1]    # strip a namespace prefix → the bare decl name
        if name and name not in seen:
            seen.add(name); out.append(name)
    return out


# ── canonical body matching / swapping ──────────────────────────────────────────────────────────────
def _body_regexes(book, prop, name):
    """The three canonical body shapes for a node, anchored at the `:=`. The WIRED shape requires the
    called helper to be THIS node's own helper (helper_<book>_<prop>_<name>) — so a real proof-local
    `have` that merely calls some *other* helper is NOT mistaken for a wired node."""
    helper = re.escape(helper_name(book, prop, name))
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


def find_body(src, sep_idx, book, prop, name):
    """`sep_idx` is the index of a node's `:=`. Match the canonical body anchored there. Return
    (state, start, end) where state ∈ {sorry,trace,wired} and src[start:end] is the whole body
    (from `:=`). Return None if no canonical shape matches (⟹ not a pipeline node)."""
    for state, rx in _body_regexes(book, prop, name):
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
    prop = prop_num(path)
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
        body = find_body(src, sep, book, prop, name)
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
        body = find_body(src, sep, book, prop, name)
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
    """Parse `theorem helper_<book>_<prop>_<name> (binders…) : claim :=` in its backing file and return
    `(objs, n_hyps)`: the ordered list of OBJECT argument names (binders whose type is a geometric
    sort Point/Line/Circle) and the COUNT of hypothesis (Prop-typed) binders, grouped-binder aware
    (`(h1 h2 : T)` counts 2). The wire fully-applies the helper by passing `objs` positionally and one
    `(by assumption)` per hypothesis binder (see `wired_body`). ABORT LOUD if the theorem is
    missing/misnamed, or a binder's type LOOKS like a sort but isn't a known one (don't guess)."""
    src = open(path, encoding="utf-8").read()
    expected = helper_name(book, prop_num(path), name)
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


def wired_body(book, prop, name, objs, n_hyps):
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
    return f":= by euclid_apply ({helper_name(book, prop, name)} {args}); (try split_ands) <;> assumption"


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
            f"{len(node.args)} arg(s) {node.args} but {helper_name(book, prop_num(propdir), node.name)} "
            f"takes {len(binders)} object binder(s) {binders}. The override must list EXACTLY the object "
            f"args, in order.")
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
        body = wired_body(book, prop_num(propdir), node.name, objs, n_hyps)
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


def strip_linter_opts(src):
    """Remove the Phase-C linter-suppression lines (whole line each). For --unwire (back to dev state)."""
    return LINTER_RE.sub("", src)


def add_linter_opts(src):
    """Insert the two `set_option linter.… false` lines once, right after the LAST import (file-level
    options apply to the rest of the file). Idempotent. For Phase-C wire — silences the cosmetic
    unused-variable / unnecessary-`<;>` warnings the generated wired form produces."""
    if LINTER_RE.search(src):
        return src
    last = None
    for m in re.finditer(r"^[ \t]*import[ \t]+\S+[ \t]*\r?\n", src, re.MULTILINE):
        last = m
    if last:
        return src[:last.end()] + LINTER_LINES + src[last.end():]
    return LINTER_LINES + src                            # no imports (unusual) — prepend


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


def _invalidate_target(target):
    """SELF-HEAL: delete the build artifacts of `target` so its NEXT build recompiles CLEAN. Called
    ONLY when a build was SIGKILL'd (wall-timeout or Ctrl-C/SIGTERM) — a kill can land mid-write of the
    `.olean`, leaving a stale/corrupt artifact that the incremental `lake build` would then trust (the
    phantom `tactic 'assumption' failed` on all-sorry source: an interrupted SP build left a WIRED olean
    while `restore_files` reverted the SOURCE to sorry). `restore_files` guards source bytes, NOT
    `.lake/build/`, so we purge the artifact here instead.

    TARGET-ONLY (never a blanket `lake clean`): builds are serialized per-prop (build.lock), so exactly
    ONE `lake build <target>` is in flight at a kill — only THAT target can be half-written. With deps
    already warm, a walled build compiles only `target` itself, so invalidating `target` fully
    self-heals while every other olean (SystemE, cited props) stays cached. (A dependency itself
    mid-compile at the kill is the lone residual case — rare, deps are warm — recovered by a manual
    `lake clean`; we do NOT auto-clean deps, which would nuke warm SystemE.)

    Best-effort: any failure here is swallowed so it can NEVER mask the real timeout/interrupt result.
    Per-target glob `<base>.*` in both lib/ and ir/ → sibling targets in the same dir are untouched."""
    try:
        rel = target.replace(".", os.sep)              # Book2.Prop03.Main → Book2/Prop03/Main
        base = os.path.basename(rel)
        sub = os.path.dirname(rel)
        for kind in ("lib", "ir"):
            d = os.path.join(BOOK_ROOT, ".lake", "build", kind, sub)
            for p in glob.glob(os.path.join(d, base + ".*")):
                try:
                    os.remove(p)
                except OSError:
                    pass
        # SILENT by design: this is internal cache hygiene (like lake's own incremental caching), not a
        # result the agent acts on. Printing it on every SP/--context only adds noise and has misled
        # readers into treating routine purges as "interrupted build" failures. Set LEANEUCLID_DEBUG=1
        # to surface it when diagnosing the cache itself.
        if os.environ.get("LEANEUCLID_DEBUG"):
            print(f"[faithful_lib] purged stale artifacts for {target} (transient/interrupted build) — "
                  f"next build recompiles clean.", flush=True)
    except Exception:
        pass                                           # invalidation is cleanup; never raise


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
        _invalidate_target(target)                     # SIGKILL may have left a half-written olean
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
                _invalidate_target(target)             # Ctrl-C/SIGTERM also kills mid-write → purge
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
    trace_state'd — the real Main/step files always end byte-identical to how they started.

    On restore, ALSO invalidate each reverted file's compiled artifact. `restore_files` wraps ONLY the
    transient-swap builds (SP / `--context`): the file was momentarily WIRED or `trace_state`'d on disk,
    lake compiled an olean against THAT transient source, and we then revert the source. That olean is
    stale by construction — if left in `.lake/`, the next incremental build trusts it and an all-sorry
    container fails with a phantom `tactic 'assumption' failed` (a wired-body tactic) against clean
    source. Purging it here (every revert path: normal exit, exception, signal) makes a transient-built
    olean impossible to inherit, regardless of whether the build completed or was interrupted."""
    def __init__(self, paths):
        self.snap = {p: open(p, "rb").read() for p in paths}
        self._prev = {}

    def restore(self):
        for p, b in self.snap.items():
            with open(p, "wb") as f:
                f.write(b)
            _invalidate_target(target_of(p))   # olean was built against transient (wired/trace) source
                                               # we just reverted → stale by construction; never trust it

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
def integrity_scan(propdir, names=None):
    """Source-only, NO builds. Verify the naming law and dev-state invariants. Returns a list of
    human-readable problem strings (empty ⟹ structurally sound). Raises FaithfulError only on a parse
    failure so malformed source is never silently accepted.

    `names` SCOPES the scan to a node set (and the files those nodes touch — their backing files + the
    containers they're wired in). When None (the default, used by `--all`/`--check`), the WHOLE prop is
    scanned. `--subtree <root>` passes Cone(root) so a not-yet-started sibling step elsewhere in the prop
    (e.g. a mapped-but-unbacked `stepN`) doesn't abort an audit of an unrelated, finished cone."""
    book = book_num(propdir)
    problems = []
    occ = parse_occurrences(propdir)
    if names is not None:
        occ = {n: o for n, o in occ.items() if n in names}
        # the files this scoped scan inspects: each in-scope node's backing file + every container it's
        # wired in (exactly the files the matching subtree audit touches).
        scoped_files = set()
        for name, occs in occ.items():
            bf = backing_file(propdir, name)
            if bf is not None:
                scoped_files.add(os.path.realpath(bf))
            for nd in occs:
                scoped_files.add(os.path.realpath(nd.file))
        files_to_scan = sorted(scoped_files)
    else:
        files_to_scan = prop_files(propdir)
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
    for path in files_to_scan:
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


# ── criterion-3 dependency check (SOURCE-REGEX, number-only — agent-facing; NOT the olean authority) ──
# Mirrors check_faithful.py's CITE; NUMBER-ONLY by design (book authentication is the human's gate-C olean
# check `check_faithful.sh`). A cited `[Prop.~B.N]` in a sentence's text is satisfied iff EITHER:
#   (construction arm) Main applies `proposition_N` (or a named construction) WITH `as` — i.e. it produces
#       objects. `as` is the deterministic grammar marker (Solve.lean: `euclid_apply term as ident(s)`),
#       so this is exact, not a heuristic. Constructions legitimately sit anywhere in Main (objects are
#       needed early), so this arm is presence-in-MAIN, NOT block-scoped — that is what correctly accepts
#       a construction introduced before the sentence that cites it (e.g. Prop03 2.3.3 cites Prop.1.31,
#       whose `proposition_31 … as AF` sits earlier because `AF` feeds `f`).
#   (proof arm) the sentence's helper CONE (stepN.lean + transitive sub-files) applies `proposition_N`
#       via `euclid_apply` (no `as`) — a proof-internal citation, recorded for olean by euclid_apply.
CITE_RE = re.compile(r'\[Prop\.~(\d+)\.(\d+)\]')
# euclid_apply (…term…) as …   → a CONSTRUCTION (binds objects). Capture the term to pull proposition_N.
APPLY_AS_RE = re.compile(r'euclid_apply\s*\((.*?)\)\s*as\b', re.DOTALL)
# euclid_apply (…term…)  NOT followed by `as`  → a proof-internal application.
APPLY_NOAS_RE = re.compile(r'euclid_apply\s*\((.*?)\)(?!\s*as\b)', re.DOTALL)
PROP_NUM_RE = re.compile(r'proposition_(\d+)')
# a sentence head that ALSO captures the Euclid text (SENTENCE_HEAD drops it); Main-only scan.
SENTENCE_TEXT_RE = re.compile(
    r'euclid_(?:sentence|intro_sentence|conclude_sentence)\s*"((?:[^"\\]|\\.)*)"\s*"((?:[^"\\]|\\.)*)"')


def _prop_nums_in(terms):
    """All proposition NUMBERS named across an iterable of `euclid_apply` term strings."""
    out = set()
    for t in terms:
        out.update(int(n) for n in PROP_NUM_RE.findall(t))
    return out


def construction_nums(propdir):
    """Number set of every `proposition_N` applied WITH `as` in Main (the construction arm)."""
    src = blank_comments(open(main_file(propdir), encoding="utf-8").read())
    return _prop_nums_in(APPLY_AS_RE.findall(src))


def _cone_proof_nums(propdir, stepname):
    """Number set of every `proposition_N` applied WITHOUT `as` across stepname's helper cone
    (its backing file + transitive sub-files). The proof arm for that sentence."""
    nums = set()
    for nm in cone_names(propdir, stepname):
        bf = backing_file(propdir, nm)
        if bf is None:
            continue
        src = blank_comments(open(bf, encoding="utf-8").read())
        nums |= _prop_nums_in(APPLY_NOAS_RE.findall(src))
    return nums


def dependency_problems(propdir):
    """SOURCE-REGEX criterion-3 check for PHASE B (both arms — helpers exist by now). Returns a list of
    hard violations: a cited `[Prop.~B.N]` satisfied by NEITHER the construction arm (`proposition_N`
    applied `… as …` anywhere in Main) NOR the proof arm (`proposition_N` `euclid_apply`'d, no `as`, in
    the citing sentence's helper cone). NUMBER-ONLY — book authentication is the gate-C olean check
    (`check_faithful.sh`). NO build, NO olean.
    (Phase A — when no helpers exist yet — uses `check_faithful.py` source mode, which checks ONLY the
    construction arm and DEFERS proof-internal citations; this both-arms check is the Phase-B gate, run
    via `check_step --dependency` and inside `--all`/`--check`.)"""
    cons = construction_nums(propdir)
    main_src = open(main_file(propdir), encoding="utf-8").read()
    # map each logical sentence's step-node name → so we can scope the proof arm to its cone
    occ = parse_occurrences(propdir)
    name_by_loc = {nd.loc: nm for nm, nds in occ.items() for nd in nds
                   if nd.kind == "sentence" and nd.loc is not None}
    problems = []
    for m in SENTENCE_TEXT_RE.finditer(blank_comments(main_src)):
        loc, text = m.group(1), m.group(2)
        for cb, cn in CITE_RE.findall(text):
            num = int(cn)
            if num in cons:
                continue                                        # construction arm — satisfied
            stepname = name_by_loc.get(loc)                     # structural sentences have no node → skip proof arm
            if stepname is not None and num in _cone_proof_nums(propdir, stepname):
                continue                                        # proof arm — satisfied
            problems.append(
                f"sentence {loc} cites [Prop.~{cb}.{cn}] but no `proposition_{cn}` is (a) applied "
                f"`… as …` in Main (construction) NOR (b) `euclid_apply`'d in its helper cone "
                f"({stepname or 'structural sentence — must be a Main construction'}).")
    return problems


# ── certification manifest (incremental "what's certified / what to recheck after an edit") ───────────
# A per-prop JSON sidecar recording, for each node the audit certified, the HASHES of that node's INPUT
# files (the small fixed set its checks read). Because the SF/SP/P checks are mutually isolated, a node's
# certificate stays valid iff NONE of its input files changed — and there is NO transitive cascade (a
# grandparent builds against the parent's signature in parent.lean, untouched; a grandchild against the
# child's file, untouched). So diffing input-file hashes is a COMPLETE, BOUNDED answer to "after editing
# file X, which nodes must I re-check?". The manifest is written ONLY by audits (--all/--subtree/per-node
# pass); `--whatchanged` is pure-read. It lives under `.lake/` (git-ignored; invisible to integrity_scan,
# which scans only *.lean), keyed exactly like prop_lock so it never collides across props.
def file_sha(path):
    """sha256 hex of a file's bytes, or None if it doesn't exist (a deleted/never-seen input)."""
    if path is None or not os.path.exists(path):
        return None
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def cert_path(propdir):
    """The manifest JSON path for this prop: `.lake/faithful-certified/<key>.json` (same <key> as
    prop_lock). `.lake/` is git-ignored, so the sidecar never shows up in git or in integrity_scan."""
    key = os.path.relpath(propdir, BOOK_ROOT).replace(os.sep, "_")
    d = os.path.join(BOOK_ROOT, ".lake", "faithful-certified")
    os.makedirs(d, exist_ok=True)
    return os.path.join(d, f"{key}.json")


def node_inputs(propdir, name, occs):
    """The set of input files whose bytes a node's certificate depends on, as BOOK_ROOT-relative paths:
      {backing_file(name)}                       — its own proof (P) / combine bytes
      ∪ {occ.file for occ in occs[name]}         — every container it's wired in (its SP context per site)
    Editing any of these invalidates `name`'s certificate; editing a file NOT in any node's input set
    invalidates nothing. (A node wired inside container C has C in its inputs ⟹ editing C flags both C's
    own node and every child wired in C — exactly {X, its children} for an edit to X, with parents covered
    because re-checking the child re-runs its SP at C.) `occs` = parse_occurrences(propdir)."""
    files = set()
    bf = backing_file(propdir, name)
    if bf is not None:
        files.add(os.path.relpath(os.path.realpath(bf), BOOK_ROOT))
    for nd in occs.get(name, []):
        files.add(os.path.relpath(os.path.realpath(nd.file), BOOK_ROOT))
    return sorted(files)


def read_manifest(propdir):
    """Load the manifest dict, or {} if absent/unreadable/corrupt (never raises — a bad manifest just
    means 'nothing known yet, re-audit')."""
    p = cert_path(propdir)
    if not os.path.exists(p):
        return {}
    try:
        with open(p, encoding="utf-8") as f:
            m = json.load(f)
        return m if isinstance(m, dict) else {}
    except (ValueError, OSError):
        return {}


def write_manifest(propdir, manifest):
    """Persist the manifest dict as pretty JSON (atomic-ish: write a temp then replace)."""
    p = cert_path(propdir)
    tmp = p + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(manifest, f, indent=2, sort_keys=True)
        f.write("\n")
    os.replace(tmp, p)
