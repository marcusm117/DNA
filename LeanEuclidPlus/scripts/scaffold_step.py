#!/usr/bin/env python3
"""Create a skeleton backing file for a Main sentence node.

After faithful-map (Phase A), this script generates the boilerplate backing file
for a single step, pre-filling the theorem name and claim type.

Usage: python3 scripts/scaffold_step.py Book2/Prop09 step1
"""
import sys
import os

sys.path.insert(0, os.path.dirname(__file__))
import faithful_lib as L


def main():
    if len(sys.argv) != 3:
        print("Usage: python3 scripts/scaffold_step.py <propdir> <node_name>")
        print("Example: python3 scripts/scaffold_step.py Book2/Prop09 step1")
        sys.exit(1)

    propdir_arg, node_name = sys.argv[1], sys.argv[2]

    try:
        propdir = L.propdir_of(propdir_arg)
    except L.FaithfulError as e:
        print(f"FAIL: {e}")
        sys.exit(2)

    book = L.book_num(propdir)
    prop = L.prop_num(propdir)

    # Parse Main to find the node
    try:
        nodes = L.parse_nodes_in_file(L.main_file(propdir), book)
    except L.FaithfulError as e:
        print(f"FAIL: {e}")
        sys.exit(2)

    node = next((n for n in nodes if n.name == node_name), None)
    if not node:
        known = ', '.join(n.name for n in nodes)
        print(f"FAIL: no node '{node_name}' in Main. Known: {known}")
        sys.exit(2)

    # Target path
    target = os.path.join(propdir, f"{node_name}.lean")
    if os.path.exists(target):
        print(f"FAIL: {os.path.relpath(target, L.BOOK_ROOT)} already exists. Not overwriting.")
        sys.exit(1)

    # Write skeleton
    helper_name = L.helper_name(book, prop, node_name)
    namespace = f"Elements.Book{book}"
    prop_rel = os.path.relpath(propdir, L.BOOK_ROOT)
    content = f"""import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace {namespace}

set_option systemE.solverTime 30 in
-- TODO: fill object/hypothesis binders (run --context {node_name})
theorem {helper_name} : {node.claim} := by sorry

end {namespace}
"""

    os.makedirs(os.path.dirname(target), exist_ok=True)
    with open(target, "w", encoding="utf-8") as f:
        f.write(content)

    print(f"OK: created {os.path.relpath(target, L.BOOK_ROOT)}")
    print(f"  Next: python3 scripts/check_step.py {prop_rel} --context {node_name}")


if __name__ == "__main__":
    main()
