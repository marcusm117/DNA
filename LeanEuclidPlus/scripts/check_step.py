#!/usr/bin/env python3
"""PHASE B verifier for the faithful pipeline. The agent's ONLY build tool in Phase B (raw
`lake`/`safe_build` are hard-denied to the agent; this owns every build, always wall-capped).

It NEVER leaves a file modified — every swap is reverted (atomic, even on Ctrl-C). The agent uses it
to run the recursive SF/SP/P recipe (see the faithful-prove skill); the human re-runs `--all` as gate B.

USAGE  (run from LeanEuclidPlus/):
  python3 scripts/check_step.py <propdir> <node>        DEFAULT: run SF → SP → P in order, stop at first
                                                          failure (this is the command the agent uses).
  python3 scripts/check_step.py <propdir> <N>           shorthand for node `step<N>` (e.g. 5 → step5)
  python3 scripts/check_step.py <propdir> --sufficient <node>   just SF (claim well-typed + sufficient)
  python3 scripts/check_step.py <propdir> --suppliable <node>   just SP (parent supplies the hyps)
  python3 scripts/check_step.py <propdir> --provable   <node>   just P  (backing file builds; reports
                                                                  zero-sorry, or sorry file:lines)
  python3 scripts/check_step.py <propdir> --provable            (NO node) build Main, tolerate sorry —
                                                                  the Phase-A skeleton-elaborates check
                                                                  (Main has no parent, so no SF/SP).
  python3 scripts/check_step.py <propdir> --context <node>   print the real hypotheses available at <node>
  python3 scripts/check_step.py <propdir> --all         FINAL bottom-up audit (SP+P, sub-nodes first);
                                                          STOP at the first failure. Run ONCE, at the end.
  python3 scripts/check_step.py <propdir> --check        instant source-only integrity scan (NO builds)

  <propdir> is e.g. Book2/Prop04  (or Book2/Prop04/Main.lean).

THE THREE PER-NODE CHECKS (node X, parent container Cnt, backing file X.lean):
  SF — SUFFICIENT : build Cnt with X's body `:= by sorry` (no wiring, no import; backing file need not
      exist). Green ⟹ X's CLAIM is well-typed in Cnt and closes its goal. Cheapest; uses ONLY the claim.
  SP — SUPPLIABLE : wire ONLY X in Cnt (body+import) → Cnt builds → revert. Uses X.lean's signature
      (objs+hyps). Green ⟹ Cnt supplies X's hypotheses. (--context only AIDS guessing them.)
  P  — PROVABLE   : build X.lean (a LEAF as-is; a CONTAINER with its sub-nodes wired) → ZERO sorry.
  The no-flag command runs SF→SP→P. `--all` runs SP+P over every node (SF is subsumed by a passing SP).
  All nodes green in `--all` ⟹ the Phase-C wired build cannot fail and is sorry-free.

Every build is wrapped in a 30s WALL timeout + the files carry a 30s SMT cap. Exceed EITHER ⟹ the node
is TOO BIG → DECOMPOSE into more backing files; NEVER raise a cap. (The lib warms a node's backing
target before the walled container build, so the wall measures the discharge, not a cold import tree.)
"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))   # so `faithful_lib` resolves from any cwd
import faithful_lib as L


# ── shared build-with-swap primitives (always revert) ───────────────────────────────────────────────
def _build_with_node_state(propdir, node, state, wall=L.WALL):
    """Put `node` into `state` (managing BOTH body and helper import), build the container, REVERT,
    return (ok, output). Atomic: the file is restored even on exception/SIGINT. When wiring, WARM the
    backing file first (no wall) so the walled container build measures only the discharge, not the
    dependency's compile."""
    book = L.book_num(propdir)
    if state == "wired":
        bf = L.backing_file(propdir, node.name)
        if bf is not None:
            L.warm_build(L.target_of(bf))
    with L.restore_files([node.file]):
        src = open(node.file, encoding="utf-8").read()
        open(node.file, "w", encoding="utf-8").write(L.set_node_state(src, node, state, propdir, book))
        return L.lake_build(L.target_of(node.file), wall=wall)
    # restore_files has restored node.file here


def check_suppliable(propdir, node):
    """S: wire ONLY this node in its container (body + helper import) → build → revert."""
    book = L.book_num(propdir)
    bf = L.backing_file(propdir, node.name)
    if bf is None:
        raise L.FaithfulError(f"node '{node.name}' has no backing file '{node.name}.lean'")
    objs = L.parse_helper_objs(bf, book, node.name)
    ok, out = _build_with_node_state(propdir, node, "wired")
    return ok, out, objs


def _backing_subnodes(propdir, node):
    """The sub-nodes (its own `have`s) inside this node's backing file — empty ⟹ it's a leaf."""
    book = L.book_num(propdir)
    bf = L.backing_file(propdir, node.name)
    return L.parse_nodes_in_file(bf, book) if bf is not None else []


def _build_file_all_wired(propdir, bf, subnodes, wall=L.WALL):
    """Wire EVERY sub-node of backing file `bf` (body + helper import), build it, REVERT. This puts the
    file in EXACTLY the state the final wired build will — so asserting it builds with ZERO sorry here
    certifies it contributes no sorry to the assembly. Atomic restore. Returns (ok, output).
    Warm each sub-node's backing target first so the walled build measures only `bf`'s own work.
    WALL=30 like every dev build — a container needing >30s with its sub-nodes wired is the decompose
    signal, NOT an uncapped pass."""
    book = L.book_num(propdir)
    for sn in subnodes:
        sbf = L.backing_file(propdir, sn.name)
        if sbf is not None:
            L.warm_build(L.target_of(sbf))
    with L.restore_files([bf]):
        # re-parse after each swap (spans/imports shift); wire to a fixed point.
        while True:
            src = open(bf, encoding="utf-8").read()
            todo = next((n for n in L.parse_nodes_in_file(bf, book) if n.state != "wired"), None)
            if todo is None:
                break
            open(bf, "w", encoding="utf-8").write(L.set_node_state(src, todo, "wired", propdir, book))
        return L.lake_build(L.target_of(bf), wall=wall)
    # restore_files has restored bf here


def check_provable(propdir, node):
    """P: build the backing file and assert ZERO sorry. Returns (status, output):
       status ∈ {'proven', 'fail', 'sorry'}.
       - LEAF backing file (no sub-nodes): build it isolated as-is.
       - CONTAINER backing file (has sub-nodes): build it with ALL its sub-nodes WIRED — the exact
         final-assembly state — so a stray `sorry` ANYWHERE in it (node or bare tactic) is caught here,
         not deferred to wire_main. (Its sub-nodes are themselves audited bottom-up, before it.)
       'sorry' ⟹ built green but a `sorry` warning remains (NOT proven)."""
    bf = L.backing_file(propdir, node.name)
    subnodes = _backing_subnodes(propdir, node)
    if subnodes:
        ok, out = _build_file_all_wired(propdir, bf, subnodes)
    else:
        ok, out = L.lake_build(L.target_of(bf), wall=L.WALL)
    if not ok:
        return "fail", out
    return ("sorry" if L.has_sorry(out) else "proven"), out


def check_sufficient(propdir, node):
    """SF: build the node's CONTAINER with the node body left `:= by sorry` (no wiring, NO helper
    import) — tolerate sorry. Green ⟹ the node's CLAIM is well-typed in the container AND closes the
    container's goal (the only remaining gap is this node's own sorry). Uses ONLY the claim as written
    in the container — NOT the backing file's signature; the backing file need not even exist yet.
    Returns (ok, output). The container is built in its current on-disk state, so this is just a build
    (reverts nothing — nothing was changed)."""
    return L.lake_build(L.target_of(node.file), wall=L.WALL)


def _sorry_locations(output):
    """Pull `<file>:<line>:<col>` from each `declaration uses 'sorry'` warning so --provable can point
    the agent at exactly where sorries remain."""
    locs = []
    for ln in (output or "").splitlines():
        if "declaration uses 'sorry'" in ln:
            m = re.search(r'([^\s]+\.lean):(\d+):(\d+)', ln)
            locs.append(f"{m.group(1)}:{m.group(2)}" if m else ln.strip())
    return locs


# ── modes ────────────────────────────────────────────────────────────────────────────────────────────
def _run_SF(propdir, node):
    """SF — Sufficient. Build the node's CONTAINER with the node's body as `sorry`. Returns ok.
    NOTE on discrimination: for a `have` node, the have is USED to close its container's goal, so SF
    genuinely tests "this claim is well-typed AND closes the goal." For a MAIN SENTENCE node, Main's
    sentences are independent `have`s that don't consume each other (the final `exact`/`rw` does), so
    building Main only confirms the sentence's claim is WELL-TYPED in scope — it does NOT isolate that
    sentence's sufficiency. SP (which wires only this sentence) is the discriminating check for Main
    sentences. We say so rather than over-claim."""
    ok, out = check_sufficient(propdir, node)
    if not ok:
        print(f"FAIL (SF — sufficient): {os.path.relpath(node.file, L.BOOK_ROOT)} did not build with "
              f"`{node.name}`'s claim as `sorry`. The claim is ill-typed in scope OR doesn't close the "
              f"goal it's used for (or the build hit the 30s cap). Fix the CLAIM before proving it.\n")
        print(_tail(out))
        return False
    if node.kind == "sentence":
        print(f"  SF ok — `{node.name}`'s claim is well-typed in Main. (Main sentences don't consume "
              f"each other, so SF only checks well-typedness here; SP isolates this sentence.)")
    else:
        print(f"  SF ok — claim well-typed in {os.path.relpath(node.file, L.BOOK_ROOT)} and sufficient "
              f"(closes the goal with `{node.name}` as sorry).")
    return True


def _run_SP(propdir, node):
    """SP — Suppliable. Returns ok."""
    ok, out, objs = check_suppliable(propdir, node)
    if not ok:
        print(f"FAIL (SP — suppliable): wiring `euclid_apply (helper_{L.book_num(propdir)}_{node.name} "
              f"{' '.join(objs)})` in {os.path.relpath(node.file, L.BOOK_ROOT)} did not build.")
        print("  → either a hypothesis isn't available at the call site (fix the signature: drop it / "
              "derive it in-body / hoist it to an earlier `have`), or the build hit the 30s cap "
              "(decompose). Build output:\n")
        print(_tail(out))
        return False
    print(f"  SP ok — hyps suppliable (objects: {' '.join(objs) or '(none)'}).")
    return True


def _run_P(propdir, node, *, verbose=True):
    """P — Provable. Returns status ∈ {'proven','sorry','fail'}; prints a report."""
    status, pout = check_provable(propdir, node)
    bf_rel = os.path.relpath(L.backing_file(propdir, node.name), L.BOOK_ROOT)
    if status == "fail":
        print(f"FAIL (P — provable): {bf_rel} did not build (or hit the 30s cap — decompose).\n")
        print(_tail(pout))
    elif status == "sorry":
        locs = _sorry_locations(pout)
        subs = _backing_subnodes(propdir, node)
        where = f" at {', '.join(locs)}" if locs else ""
        if subs:
            print(f"  P pending — {bf_rel} builds but still has `sorry`{where} (sub-nodes: "
                  f"{', '.join(s.name for s in subs)}). Certify each sub-node until none remains.")
        else:
            print(f"  P pending — {bf_rel} builds but still has `sorry`{where}. Prove it, then re-run.")
    elif verbose:
        print(f"  P ok — {bf_rel} builds with ZERO sorry (sub-nodes wired if any).")
    return status


def mode_node(propdir, node_name):
    """No-flag: run SF → SP → P in order, stopping at the first failure (the agent's default command)."""
    nodes = L.parse_all_nodes(propdir)
    node = _require_node(propdir, nodes, node_name)
    if node is None:
        return 2
    print(f"[check_step] {node_name}  ({node.kind} in {os.path.relpath(node.file, L.BOOK_ROOT)})")
    if not _run_SF(propdir, node):
        return 1
    if not _run_SP(propdir, node):
        return 1
    status = _run_P(propdir, node)
    if status == "fail":
        return 1
    if status == "sorry":
        return 0                                    # SF+SP certified; body still to prove — not an error
    print(f"PASS: {node_name} CERTIFIED (SF + SP + P).")
    return 0


def _require_node(propdir, nodes, node_name):
    if node_name not in nodes:
        print(f"FAIL: no node '{node_name}' in {os.path.relpath(propdir, L.BOOK_ROOT)}. "
              f"Known: {', '.join(sorted(nodes, key=L.natural_key))}")
        return None
    return nodes[node_name]


def mode_one(propdir, node_name, which):
    """Single-flag diagnostics: --sufficient / --suppliable / --provable for one node."""
    nodes = L.parse_all_nodes(propdir)
    node = _require_node(propdir, nodes, node_name)
    if node is None:
        return 2
    print(f"[check_step --{which}] {node_name}  ({os.path.relpath(node.file, L.BOOK_ROOT)})")
    if which == "sufficient":
        return 0 if _run_SF(propdir, node) else 1
    if which == "suppliable":
        return 0 if _run_SP(propdir, node) else 1
    # provable
    status = _run_P(propdir, node)
    return 1 if status == "fail" else 0             # 'sorry' is reported, not a hard fail in diag mode


def mode_context(propdir, node_name):
    nodes = L.parse_all_nodes(propdir)
    if node_name not in nodes:
        print(f"FAIL: no node '{node_name}'. Stub it first as `have {node_name} : <claim> := by sorry` "
              f"(or it's a Main sentence). Known: {', '.join(sorted(nodes))}")
        return 2
    node = nodes[node_name]
    ok, out = _build_with_node_state(propdir, node, "trace")
    block = _extract_trace(out, node.file)
    print(f"[check_step --context] hypotheses available at node '{node_name}' "
          f"(in {os.path.relpath(node.file, L.BOOK_ROOT)}):\n")
    if block:
        print(block)
    else:
        print("(could not isolate a trace_state block — full build output below)\n")
        print(_tail(out))
    print("\nNOTE: this is the LITERAL local context. `euclid_apply (helper…); euclid_finish` can also "
          "discharge facts NOT listed here (between/sameSide/distinctness derived by SMT). The "
          "authoritative suppliability test is SP (`check_step <node>`), not this list — do not "
          "over-decompose because something isn't shown.")
    return 0 if ok or block else 1


def mode_all(propdir):
    problems = L.integrity_scan(propdir)
    if problems:
        print("FAIL (--all aborted by integrity scan — fix structure first):")
        for p in problems:
            print("  - " + p)
        return 1
    # bottom-up over the backing-file containment relation: sub-nodes before the nodes that contain
    # them, so the first failure is always the DEEPEST broken node.
    nodes = L.audit_order(propdir)
    print(f"[check_step --all] bottom-up audit of {len(nodes)} node(s) in "
          f"{os.path.relpath(propdir, L.BOOK_ROOT)} (sub-nodes before their parents):")
    for nd in nodes:
        tag = f"{nd.name} ({os.path.relpath(nd.file, L.BOOK_ROOT)})"
        ok, out, objs = check_suppliable(propdir, nd)
        if not ok:
            print(f"  ✗ {tag}: SP FAILED (see below) — this is the deepest failure; fix it first.\n")
            print(_tail(out))
            return 1
        status, pout = check_provable(propdir, nd)
        if status == "fail":
            print(f"  ✗ {tag}: P FAILED — backing file did not build (or hit the 30s cap).\n")
            print(_tail(pout))
            return 1
        if status == "sorry":
            print(f"  ✗ {tag}: P FAILED — backing file builds but still has a `sorry` warning "
                  f"(a node or bare tactic left unproven).\n")
            print(_tail(pout))
            return 1
        print(f"  ✓ {tag}: SP + P (builds zero-sorry)")
    print(f"\nPASS: all {len(nodes)} node(s) certified — every backing file builds with ZERO sorry "
          f"(sub-nodes wired) and every node's type discharges ⇒ the Phase-C wired build is GUARANTEED "
          f"green AND sorry-free. Run `python3 scripts/wire_main.py {os.path.relpath(propdir, L.BOOK_ROOT)}`.")
    return 0


def mode_build_main(propdir):
    """`--provable` with NO node = build Main, tolerate sorry (the Phase-A skeleton elaboration check).
    Main has NO parent, so SF/SP don't apply to it — it only gets the build (the P-style "does it
    compile"), and sorry is fine because its sentence nodes are sorry. This is the all-sorry skeleton
    elaboration the agent uses in Phase A (raw safe_build is hard-denied)."""
    mf = L.main_file(propdir)
    print(f"[check_step --provable] building {os.path.relpath(mf, L.BOOK_ROOT)} (no parent; tolerating sorry)…")
    ok, out = L.lake_build(L.target_of(mf), wall=L.WALL)
    if not ok:
        print("FAIL: Main did not elaborate (or hit the 30s cap).\n")
        print(_tail(out))
        return 1
    print("OK: Main elaborates (sorry tolerated). The sentence map type-checks.")
    return 0


def mode_check(propdir):
    problems = L.integrity_scan(propdir)
    if problems:
        print(f"FAIL: {len(problems)} structural problem(s) in "
              f"{os.path.relpath(propdir, L.BOOK_ROOT)}:")
        for p in problems:
            print("  - " + p)
        return 1
    n = len(L.parse_all_nodes(propdir))
    print(f"OK: {os.path.relpath(propdir, L.BOOK_ROOT)} structurally sound — {n} node(s), naming law "
          f"holds, every node has a backing file, every file carries the 30s cap, nothing pre-wired.")
    return 0


# ── output helpers ────────────────────────────────────────────────────────────────────────────────
def _tail(out, n=40):
    lines = (out or "").rstrip().splitlines()
    return "\n".join(lines[-n:])


def _extract_trace(out, container_file):
    """Pull the trace_state block(s) out of a build log. trace_state prints
    `info: <path>:<line>:<col>:` then the hypotheses, ending at the goal line (starts with ⊢)."""
    lines = (out or "").splitlines()
    base = os.path.basename(container_file)
    blocks, i, n = [], 0, len(lines)
    info_re = re.compile(r"^info: .*:\d+:\d+:")
    while i < n:
        if info_re.match(lines[i]) and base in lines[i]:
            # strip the `info: path:line:col:` prefix from the first line, keep its trailing content
            first = re.sub(r"^info: .*?:\d+:\d+:\s*", "", lines[i])
            blk = [first] if first.strip() else []
            i += 1
            while i < n and not info_re.match(lines[i]) and not lines[i].startswith(("error:", "warning:")):
                blk.append(lines[i])
                if lines[i].lstrip().startswith("⊢"):
                    i += 1
                    break
                i += 1
            blocks.append("\n".join(blk).rstrip())
        else:
            i += 1
    return "\n\n".join(b for b in blocks if b.strip())


# ── CLI ───────────────────────────────────────────────────────────────────────────────────────────
def main(argv):
    if not argv:
        print(__doc__)
        return 2
    try:
        propdir = L.propdir_of(argv[0])
        rest = argv[1:]

        def as_node(tok):
            return f"step{tok}" if tok.isdigit() else tok

        # CONVENTION: Main is NOT a node. The only no-node operation is `--provable` (build Main, which
        # has no parent → only a build/compile check). SF/SP REQUIRE a node and FAIL loudly without one.
        def reject_main_as_node(tok):
            if tok.lower() in ("main", "main.lean"):
                print("FAIL: `Main` is NOT a node — Main has no parent, so SF/SP don't apply to it. "
                      "To build Main (the Phase-A skeleton-elaborates check) run `--provable` with NO "
                      "node. To check a SENTENCE inside Main, pass that sentence's node (e.g. step5).")
                return True
            return False

        if rest == ["--check"]:
            return mode_check(propdir)
        if rest == ["--all"]:
            return mode_all(propdir)
        if rest == ["--provable"]:                   # no node = Phase-A: build Main (no parent), tolerate sorry
            return mode_build_main(propdir)
        if rest in (["--sufficient"], ["--suppliable"]):
            abbr = "SF" if rest[0] == "--sufficient" else "SP"
            print(f"FAIL: `{rest[0]}` needs a NODE argument (e.g. `{rest[0]} step5`). "
                  f"{abbr} is a per-node check; Main has no parent so it has no SF/SP — use "
                  f"`--provable` with no node to build Main.")
            return 2
        if len(rest) == 2 and rest[0] == "--context":
            if reject_main_as_node(rest[1]):
                return 2
            return mode_context(propdir, as_node(rest[1]))
        if len(rest) == 2 and rest[0] in ("--sufficient", "--suppliable", "--provable"):
            if reject_main_as_node(rest[1]):
                return 2
            return mode_one(propdir, as_node(rest[1]), rest[0][2:])
        if len(rest) == 1 and not rest[0].startswith("-"):
            if reject_main_as_node(rest[0]):
                return 2
            return mode_node(propdir, as_node(rest[0]))
        print(__doc__)
        return 2
    except L.FaithfulError as e:
        print(f"ABORT (structural/naming error — refusing to proceed): {e}")
        return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
