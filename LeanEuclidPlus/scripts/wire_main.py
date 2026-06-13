#!/usr/bin/env python3
"""PHASE C committer for the faithful pipeline — the ONLY script that modifies real files for keeps.

Run by the HUMAN, after Phase B's gate (`check_step.py <propdir> --all` passes). That audit has already
PROVEN that wiring every node would build, so this is a mechanical witness, not a search.

USAGE  (run from LeanEuclidPlus/):
  python3 scripts/wire_main.py <propdir>            COMMIT the wiring + build Main once (uncapped)
  python3 scripts/wire_main.py <propdir> --unwire   reverse it: every node back to `:= by sorry`,
                                                      30s caps restored (return to a Phase-B state)

  <propdir> is e.g. Book2/Prop04 (or Book2/Prop04/Main.lean).

WIRE (bare): for EVERY node in EVERY file of the prop, replace `:= by sorry` with the canonical
  `euclid_apply (helper_<book>_<name> <objs>); euclid_finish`, and DELETE every
  `set_option systemE.solverTime 30 in` line (→ System E's 300s default — strictly more time than the
  30s dev cap, never less; the final build is provably correct so it needs no tight cap and no wall
  timeout). Then build `<propdir>.Main` ONCE, uncapped, under the build lock. Guaranteed green if
  `--all` passed; a `declaration uses 'sorry'` warning means a node was left unproven → its fix is in a
  backing file → `--unwire` and go back to Phase B.

This is a SEPARATE script from check_step.py (which always reverts) precisely so "verify, reverting"
and "commit the wiring" can never be confused. Both share the swap/cap logic in faithful_lib.py.
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))   # so `faithful_lib` resolves from any cwd
import faithful_lib as L


def _rewrite_file_bodies(path, propdir, book, *, wire):
    """Rewrite EVERY node body in one file (wire ↔ unwire), then RECONCILE imports + cap to the target
    state UNCONDITIONALLY (not as a side effect of a body change — a body may already be in the target
    state yet a stray import/cap remain). Re-parse after each body swap because spans shift."""
    changed = 0
    target_state = "wired" if wire else "sorry"
    while True:
        src = open(path, encoding="utf-8").read()
        nodes = L.parse_nodes_in_file(path, book)
        target = next((nd for nd in nodes if nd.state != target_state), None)
        if target is None:
            break
        open(path, "w", encoding="utf-8").write(L.set_node_state(src, target, target_state, propdir, book))
        changed += 1
    # reconcile imports UNCONDITIONALLY:
    #   wire  → ensure every node in this file has its helper import present
    #   unwire→ strip EVERY pipeline (helper/step) import (clean dev state imports none)
    src = open(path, encoding="utf-8").read()
    if wire:
        for nd in L.parse_nodes_in_file(path, book):
            bf = L.backing_file(propdir, nd.name)
            if bf is not None:
                src = L.add_import(src, L.target_of(bf))
    else:
        for mod in L.pipeline_imports(src, propdir):
            src = L.remove_import(src, mod)
    # caps: wire strips them, unwire restores
    src = L.strip_caps(src) if wire else (L.add_cap(src) if "theorem" in src else src)
    open(path, "w", encoding="utf-8").write(src)
    return changed


def wire(propdir, *, unwire):
    book = L.book_num(propdir)
    if not unwire:
        problems = L.integrity_scan(propdir)
        if problems:
            print("ABORT: prop is not in a clean Phase-B state (run `check_step --check` / `--all` "
                  "first):")
            for p in problems:
                print("  - " + p)
            return 2

    verb = "unwiring" if unwire else "wiring"
    total = 0
    for path in L.prop_files(propdir):
        total += _rewrite_file_bodies(path, propdir, book, wire=not unwire)
    print(f"[wire_main] {verb}: rewrote {total} node body(ies) across "
          f"{os.path.relpath(propdir, L.BOOK_ROOT)}"
          + ("; caps restored." if unwire else "; 30s caps deleted (→ 300s default)."))

    if unwire:
        print("Returned to a Phase-B (all-sorry) state. Re-run `check_step --all` after fixing backing "
              "files.")
        return 0

    target = L.target_of(L.main_file(propdir))
    print(f"[wire_main] building {target} once (uncapped, no wall timeout)…")
    ok, out = L.lake_build(target, wall=None)
    if not ok:
        print("FAIL: the committed wired build did NOT pass. Fix is in a backing file → "
              "`wire_main.py <propdir> --unwire` to return to Phase B.\n")
        print(out.rstrip()[-4000:])
        return 1
    if L.has_sorry(out):
        print("FAIL: build succeeded but a `declaration uses 'sorry'` warning means a node was left "
              "unproven. `--unwire` and finish Phase B.\n")
        print(out.rstrip()[-2000:])
        return 1
    print(f"PASS: {target} built green, zero sorry. Phase C wiring committed. Now run the "
          f"authoritative checks: scripts/check_faithful.sh, check_steps.py, check_signatures.py.")
    return 0


def main(argv):
    if not argv or (len(argv) == 2 and argv[1] != "--unwire") or len(argv) > 2:
        print(__doc__)
        return 2
    try:
        propdir = L.propdir_of(argv[0])
        with L.prop_lock(propdir):                   # serialize with check_step/wire_main on the SAME prop
            return wire(propdir, unwire=(len(argv) == 2 and argv[1] == "--unwire"))
    except L.FaithfulError as e:
        print(f"ABORT (structural/naming error — refusing to proceed): {e}")
        return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
