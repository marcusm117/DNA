#!/usr/bin/env python3
"""PreToolUse(Write/Edit) hook: enforce in-order step discipline for the faithful pipeline.

Agents keep writing backing files for steps beyond the current frontier (e.g. creating step12.lean
when step8 isn't certified). The skill says "don't do this" but agents ignore prose. This hook
hard-denies the file creation so the agent physically cannot skip ahead.

RULE: a file matching `Book*/Prop*/step<N>*.lean` is allowed only if step<N>'s Main-level ancestor
is AT or BEFORE the frontier (the first NOT-DONE Main node). Sub-nodes of the frontier step
are fine (e.g. step8_foo.lean when step8 is frontier). Files that don't match the step pattern
(fp.lean, Main.lean, etc.) are always allowed.

Determining the frontier:
  - Frontier = the first Main node that is NOT `done` on the status board — which means STALE
    (certified, but an input file changed) counts as not-done just like uncertified `todo`. A
    certified-but-stale node therefore HARD-STOPS work on every later step until it's re-certified
    (`check_step <prop> --subtree <node>`). This is the whole point: an agent must not skip ahead
    past a node whose proof no longer holds.
  - Computed by delegating to `faithful_lib.status_rows` (the same authoritative, build-free board
    `check_step --status` renders — pure source-parse + file-hash, no Lean/SMT) so the hook's notion
    of "done" can never drift from the board.
  - FALLBACK (if faithful_lib can't be imported / status_rows raises): a presence-only frontier —
    first Main node not in the manifest's `subtrees` keys, via a local regex parse. Fail-open: the
    hook must never crash the Write/Edit pipeline.
  - A fresh prop (no manifest, or no `subtrees` yet) allows everything — don't block step1.
"""
import sys, json, re, os

# The repo root (LeanEuclidPlus/) — same canonicalization as faithful_lib.py
_SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.realpath(os.path.join(_SCRIPT_DIR, "..", ".."))  # DNA/
_LEAN_ROOT = os.path.join(_REPO_ROOT, "LeanEuclidPlus")


def deny(reason):
    print(json.dumps({"hookSpecificOutput": {
        "hookEventName": "PreToolUse",
        "permissionDecision": "deny",
        "permissionDecisionReason": reason,
    }}))
    sys.exit(0)


def allow():
    sys.exit(0)


# Regex to extract Main-level node names from Main.lean (source order).
# Matches both `euclid_sentence "..." (stepN :` and top-level `have stepN : ... := by sorry`.
# Only nodes with `:= by sorry` bodies are pipeline nodes (real proof bodies aren't nodes).
_SENTENCE_RE = re.compile(
    r'euclid_sentence\s+"[^"]*"\s+"[^"]*"\s+\((\w+)\s*:', re.DOTALL)
_HAVE_SORRY_RE = re.compile(
    r'^[ \t]*have\s+(\w+)\s*:[^\n]*:=\s*by\s+sorry', re.MULTILINE)


def main_node_names(main_path):
    """Parse Main.lean and return Main-level node names in source order.
    Only picks up nodes with `:= by sorry` bodies (pipeline nodes)."""
    try:
        src = open(main_path, encoding="utf-8").read()
    except (OSError, IOError):
        return []

    nodes = []
    for m in _SENTENCE_RE.finditer(src):
        nodes.append((m.start(), m.group(1)))
    for m in _HAVE_SORRY_RE.finditer(src):
        name = m.group(1)
        # Skip `have`s that are deeply indented (inside a case branch, etc.)
        # The regex matches from ^ (line start), so m.start() is the first char of the line.
        # Count leading whitespace to get the indent level.
        line_start = m.start()
        indent = 0
        while line_start + indent < len(src) and src[line_start + indent] in " \t":
            indent += 1
        if indent <= 4:  # top-level Main nodes are at low indent (2-space from `by` block)
            nodes.append((m.start(), name))
    nodes.sort(key=lambda x: x[0])
    return [name for _, name in nodes]


def _presence_frontier(node_names, subtrees):
    """FALLBACK frontier: first Main node not in `subtrees` keys (presence only — staleness-blind).
    Used when the authoritative status_rows path is unavailable."""
    for name in node_names:
        if name not in subtrees:
            return name, node_names, "todo"
    return None, node_names, None  # all present


def find_frontier(propdir):
    """Return `(frontier, node_names, state)` where `frontier` is the name of the first NOT-DONE Main
    node (None if all done), `node_names` is the ordered Main node list, and `state` is the frontier's
    board state ("stale"/"todo", or None when all done) so the deny message can tailor itself.

    The frontier is staleness-AWARE: a certified-but-stale node is NOT done, so it becomes the frontier
    and blocks every later step until re-certified. Delegates to `faithful_lib.status_rows` (the same
    build-free board `check_step --status` renders), with a presence-only fallback that never raises."""
    main_path = os.path.join(propdir, "Main.lean")
    if not os.path.isfile(main_path):
        return None, [], None

    node_names = main_node_names(main_path)
    if not node_names:
        return None, [], None

    # Read the certified manifest
    rel = os.path.relpath(propdir, _LEAN_ROOT)
    manifest_key = rel.replace(os.sep, "_")
    manifest_path = os.path.join(_LEAN_ROOT, ".lake", "faithful-certified", f"{manifest_key}.json")

    try:
        with open(manifest_path, encoding="utf-8") as f:
            manifest = json.load(f)
    except (OSError, IOError, json.JSONDecodeError):
        # No manifest = fresh prop or .lake/ wiped — allow everything (re-cert needed, not deletion)
        return None, node_names, None

    subtrees = manifest.get("subtrees", {})

    # Only enforce when there's genuine partial progress (at least one subtree cert)
    if not subtrees:
        return None, node_names, None

    # AUTHORITATIVE path: ask status_rows which node is the first not-done (stale OR todo). This is
    # pure source-parse + file-hash (no build). Fail-open to the presence-only frontier on any error.
    try:
        sys.path.insert(0, os.path.join(_LEAN_ROOT, "scripts"))
        import faithful_lib as L
        rows, _checks = L.status_rows(propdir)
        if rows:
            board_names = [r[0] for r in rows]
            for name, state, _detail in rows:
                if state != "done":
                    return name, board_names, state
            return None, board_names, None  # every node done
    except Exception:
        pass  # fall through to presence-only frontier

    return _presence_frontier(node_names, subtrees)


def main_level_ancestor(filename, node_names):
    """Given a step filename like 'step8_foo.lean', find which Main-level node it belongs to.
    Returns the Main node name (e.g. 'step8') or None if it doesn't match any."""
    base = os.path.splitext(filename)[0]  # e.g. 'step8_foo'

    # Try longest prefix match against Main node names
    # Sort by length descending so 'step10' matches before 'step1'
    for name in sorted(node_names, key=len, reverse=True):
        if base == name or base.startswith(name + "_"):
            return name

    return None


def main():
    try:
        data = json.load(sys.stdin)
    except Exception:
        allow()

    file_path = (data.get("tool_input") or {}).get("file_path") or ""
    if not file_path:
        allow()

    # Canonicalize
    file_path = os.path.realpath(file_path)

    # Only gate files in Book*/Prop*/ directories
    # Check if this is under LeanEuclidPlus/Book*/Prop*/
    rel = None
    try:
        rel = os.path.relpath(file_path, _LEAN_ROOT)
    except ValueError:
        allow()

    if rel is None or rel.startswith(".."):
        allow()

    # Match pattern: Book<N>/Prop<NN>/<something>.lean
    parts = rel.replace("\\", "/").split("/")
    if len(parts) < 3:
        allow()

    book_dir = parts[0]   # e.g. 'Book2'
    prop_dir = parts[1]   # e.g. 'Prop14'
    filename = parts[2]   # e.g. 'step12.lean'

    if not (re.match(r"Book\d+$", book_dir) and re.match(r"Prop\d+$", prop_dir)):
        allow()

    if not filename.endswith(".lean"):
        allow()

    # Always allow Main.lean itself
    if filename == "Main.lean":
        allow()

    # Determine the prop directory and frontier
    propdir = os.path.join(_LEAN_ROOT, book_dir, prop_dir)
    frontier, node_names, frontier_state = find_frontier(propdir)

    # If no Main.lean or no nodes (Phase A not done), allow everything
    if not node_names:
        allow()

    # If all certified (frontier is None), allow everything
    if frontier is None:
        allow()

    # Find which Main-level node this file belongs to
    ancestor = main_level_ancestor(filename, node_names)

    if ancestor is None:
        # Doesn't match any known Main node — could be a typo or future node. Deny to be safe.
        deny(f"'{filename}' does not match any Main-level node in {book_dir}/{prop_dir}. "
             f"Known nodes: {', '.join(node_names)}. Check the filename.")

    # Check if ancestor is at or before the frontier
    try:
        ancestor_idx = node_names.index(ancestor)
        frontier_idx = node_names.index(frontier)
    except ValueError:
        allow()  # shouldn't happen, but be safe

    if ancestor_idx <= frontier_idx:
        # At or before the frontier — allowed
        allow()
    else:
        # BEYOND the frontier — denied. Tailor the wording to WHY the frontier isn't done.
        if frontier_state == "stale":
            why = (f"the current frontier '{frontier}' is STALE — it was certified, but one of its "
                   f"input files changed, so its proof must be re-confirmed before any later step")
        else:
            why = f"the current frontier '{frontier}' is not yet certified"
        deny(f"IN-ORDER DISCIPLINE: '{ancestor}.lean' is for Main node '{ancestor}' which is AFTER "
             f"{why}. Re-certify it first — the systematic way is "
             f"`python3 scripts/check_step.py {book_dir}/{prop_dir} --drive` (it re-runs the first "
             f"not-done node, which is '{frontier}', then continues in order); or surgically "
             f"`--subtree {frontier}`. Finish steps IN ORDER — do not skip ahead.")


if __name__ == "__main__":
    main()
