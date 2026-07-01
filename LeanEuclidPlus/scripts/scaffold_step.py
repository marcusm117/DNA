#!/usr/bin/env python3
"""Create a skeleton backing file for a pipeline node — a Main `euclid_sentence` step OR a `have`
sub-node introduced during decomposition (Phase B).

Given where the node lives, this writes `<node>.lean` in the prop dir with the correct imports, the
30s dev cap, the naming-law theorem header (`helper_<book>_<prop>_<node>`), and the claim type
pre-filled from wherever the node is declared. So the agent never hand-types the boilerplate — it
only fills the object/hypothesis binders and the proof body. For a Main sentence carrying
`-- @assumption` lines, the reasoning hyps are pre-populated as `(hassumpK : T)` binders.

Usage:
  python3 scripts/scaffold_step.py <file-or-propdir> <node>

  <file>    a `.lean` file that DECLARES <node> (a Main.lean euclid_sentence, or a stepK.lean `have`)
            — the script parses THIS file, figures out sentence-vs-`have`, and reads the claim.
  <propdir> e.g. Book1/Prop18 — the script auto-locates <node> anywhere in the prop tree.

Examples:
  python3 scripts/scaffold_step.py Book2/Prop09/Main.lean step1       # a Main sentence
  python3 scripts/scaffold_step.py Book2/Prop09/step5.lean step5_bgd  # a `have` sub-node in step5
  python3 scripts/scaffold_step.py Book2/Prop09 step1                 # auto-locate across the tree
"""
import sys
import os

sys.path.insert(0, os.path.dirname(__file__))
import faithful_lib as L


def find_node(arg, node_name):
    """Locate the node. `arg` is either a `.lean` file that declares it, or a propdir to search.

    Returns (node, propdir_abs, book, prop)."""
    if arg.endswith(".lean"):
        abspath = arg if os.path.isabs(arg) else os.path.join(L.BOOK_ROOT, arg)
        if not os.path.exists(abspath):
            raise L.FaithfulError(f"file not found: {arg}")
        propdir = os.path.dirname(abspath)
        book = L.book_num(propdir)
        nodes = L.parse_nodes_in_file(abspath, book)
        node = next((n for n in nodes if n.name == node_name), None)
        if not node:
            known = ', '.join(n.name for n in nodes) or "(none)"
            raise L.FaithfulError(f"no node '{node_name}' in {arg}. Known here: {known}")
        return node, propdir, book, L.prop_num(propdir)

    # propdir form: locate the node anywhere in the prop tree (Main sentence or shared `have`).
    propdir = L.propdir_of(arg)
    book = L.book_num(propdir)
    occ = L.parse_occurrences(propdir)
    if node_name not in occ:
        known = ', '.join(sorted(occ)) or "(none)"
        raise L.FaithfulError(f"no node '{node_name}' in the {arg} tree. Known: {known}")
    return occ[node_name][0], propdir, book, L.prop_num(propdir)


def main():
    if len(sys.argv) != 3:
        print("Usage: python3 scripts/scaffold_step.py <file-or-propdir> <node>")
        print("Examples:")
        print("  python3 scripts/scaffold_step.py Book2/Prop09/Main.lean step1")
        print("  python3 scripts/scaffold_step.py Book2/Prop09/step5.lean step5_bgd")
        print("  python3 scripts/scaffold_step.py Book2/Prop09 step1")
        sys.exit(1)

    arg, node_name = sys.argv[1], sys.argv[2]

    try:
        node, propdir, book, prop = find_node(arg, node_name)
    except L.FaithfulError as e:
        print(f"FAIL: {e}")
        sys.exit(2)

    # Target path (always in the prop dir; naming law: node ≡ file ≡ helper_<book>_<prop>_<node>).
    target = os.path.join(propdir, f"{node_name}.lean")
    if os.path.exists(target):
        print(f"FAIL: {os.path.relpath(target, L.BOOK_ROOT)} already exists. Not overwriting.")
        sys.exit(1)

    helper_name = L.helper_name(book, prop, node_name)
    namespace = f"Elements.Book{book}"
    prop_rel = os.path.relpath(propdir, L.BOOK_ROOT)
    kind_label = "euclid_sentence step" if node.kind == "sentence" else "`have` sub-node"

    # Build pre-populated assumption binder lines (Main sentences only; `have` nodes have none).
    assump_lines = ""
    if node.assumptions:
        lines = ["  -- Reasoning hypotheses (from @assumption — keep these types in the signature):"]
        for i, (text, atype, _override) in enumerate(node.assumptions, 1):
            lines.append(f'  (hassump{i} : {atype})   -- "{text}"')
        assump_lines = "\n" + "\n".join(lines) + "\n"

    if assump_lines:
        thm_sig = f"theorem {helper_name}{assump_lines}  : {node.claim} := by sorry"
    else:
        thm_sig = f"theorem {helper_name} : {node.claim} := by sorry"

    content = f"""import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace {namespace}

set_option systemE.solverTime 30 in
-- TODO: fill object/hypothesis binders (run --context {node_name})
{thm_sig}

end {namespace}
"""

    os.makedirs(os.path.dirname(target), exist_ok=True)
    with open(target, "w", encoding="utf-8") as f:
        f.write(content)

    print(f"OK: created {os.path.relpath(target, L.BOOK_ROOT)}  ({kind_label} '{node_name}')")
    print(f"  Next: python3 scripts/check_step.py {prop_rel} --context {node_name}")


if __name__ == "__main__":
    main()
