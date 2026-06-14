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
  python3 scripts/check_step.py <propdir> --provable   <node>   just P  (LEAF builds zero-sorry; a
                                                                  CONTAINER node reports n/a = PASS)
  python3 scripts/check_step.py <propdir> --provable            (NO node) build Main, tolerate sorry —
                                                                  the Phase-A skeleton-elaborates check
                                                                  (Main has no parent, so no SF/SP).
  python3 scripts/check_step.py <propdir> --context <node>   print the real hypotheses available at <node>
  python3 scripts/check_step.py <propdir> --subtree <node>  audit the node's WHOLE CONE (it + every
                                                          sub-node it transitively contains), bottom-up,
                                                          scoped to the cone — does NOT touch other
                                                          steps. Confirms a container/step is done.
  python3 scripts/check_step.py <propdir> --all         FINAL bottom-up audit of the WHOLE prop (SP all +
                                                          P leaves + no-stray-sorry; sub-nodes first);
                                                          STOP at first failure. Run ONCE, at the very end.
  python3 scripts/check_step.py <propdir> --check        instant source-only integrity scan (NO builds;
                                                          incl. no-stray-sorry: every sorry/admit/axiom
                                                          must be a declared node body; + criterion-3 deps)
  python3 scripts/check_step.py <propdir> --dependency   instant criterion-3 check (NO builds): every cited
                                                          [Prop.~B.N] satisfied by a Main construction
                                                          (`… as …`) OR its sentence's helper cone. Number-
                                                          only; the human's gate-C olean check is book-aware
                                                          — don't game it. (`--deps` alias; `--all` also runs it.)

  <propdir> is e.g. Book2/Prop04  (or Book2/Prop04/Main.lean).

THE CHECKS (node X, parent container Cnt, backing file X.lean):
  SF — SUFFICIENT : build Cnt with X's body `:= by sorry` (no wiring, no import; backing file need not
      exist). Green ⟹ X's CLAIM is well-typed in Cnt and closes its goal. Cheapest; uses ONLY the claim.
  SP — SUPPLIABLE (ISOLATED, O(1), no SMT) : wire ONLY X in Cnt (`euclid_apply (helper X-objs
      (by assumption)…); (try split_ands) <;> assumption`); ALL other nodes + the combine tail stay
      `sorry`; X.lean warmed SIGNATURE-ONLY. Green ⟹ Cnt supplies X's hypotheses — each `(by assumption)`
      is an exact TYPE-match against the context (so a hyp must match the EXACT shape the context has;
      `(by assumption)` does NOT crack a conjunction). Body- and combine-independent. (--context AIDS.)
  COMBINE — (CONTAINERS ONLY) : build Cnt's backing file in dev state (sub-nodes sorry, REAL combine
      tail), tolerate sorry. Green ⟹ the combine closes from the sub-node claim-types.
  P  — PROVABLE   : LEAVES ONLY — build X.lean isolated → ZERO sorry. A CONTAINER backing file is NOT
      P-built ('container' = n/a): its combine is certified by its OWN combine-check, its leaves by P.
  The no-flag command `check_step <node>` certifies ONLY that node (SF/SP, + P if leaf / Combine if
  container) — NOT its sub-nodes. To confirm a CONTAINER/step's whole subtree, use `--subtree <node>`
  (SP every in-cone call site + Combine every in-cone container + P every leaf, bottom-up). `--all` does
  this for the WHOLE prop + a no-stray-sorry scan. All green in `--all` ⟹ the Phase-C wired build cannot
  fail and is sorry-free: every SMT query in that build is one already measured ≤30s by a leaf-P or a
  combine-check, and every wire discharges by SMT-free `assumption`.
  DRIVING ORDER: leaves first (bare `check_step`), then `--subtree` each container/step bottom-up (only
  after its components pass), then `--all` ONCE at the very end. NEVER run `--all` to find a failure.

Every build is wrapped in a 30s WALL timeout + the files carry a 30s SMT cap. Exceed EITHER ⟹ the node
is TOO BIG → DECOMPOSE into more backing files; NEVER raise a cap.
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


def _build_isolated_sp(propdir, node, wall=L.WALL):
    """ISOLATED SP build of `node`: wire ONLY this node in its container; leave ALL other nodes dev
    `:= by sorry`; replace the container's COMBINE TAIL with `sorry`; and warm this node's backing
    olean SIGNATURE-ONLY (its theorem body → `:= by sorry`). So the build exercises EXACTLY this node's
    wire (its `(by assumption)` discharges) — O(1), no SMT, and independent of the node's proof body AND
    the container's combine. Both the signature-only backing file and the isolated container are written
    under one `restore_files` window, so both hold during the SAME build and both revert. Returns
    (ok, output)."""
    book = L.book_num(propdir)
    bf = L.backing_file(propdir, node.name)
    files = [node.file] + ([bf] if bf is not None and os.path.realpath(bf) != os.path.realpath(node.file) else [])
    with L.restore_files(files):
        # 1) signature-only-warm the backing olean (so the wire's `import` resolves to a type, no body build)
        if bf is not None:
            bsrc = open(bf, encoding="utf-8").read()
            open(bf, "w", encoding="utf-8").write(L.set_theorem_body_sorry(bsrc))
            L.warm_build(L.target_of(bf))                       # sorry tolerated — dependency olean only
        # 2) write the isolated-SP transform to the container and build it (walled)
        csrc = open(node.file, encoding="utf-8").read()
        nodes = L.parse_nodes_in_file(node.file, book)
        open(node.file, "w", encoding="utf-8").write(
            L.set_node_isolated_sp(csrc, node, nodes, propdir, book))
        return L.lake_build(L.target_of(node.file), wall=wall)
    # restore_files has restored node.file AND the backing file here


def check_suppliable(propdir, node):
    """SP — ISOLATED: wire ONLY this node (objects + one `(by assumption)` per hyp + structural closer);
    every other node + the combine tail stay `sorry`; backing olean warmed signature-only. Green ⟺ the
    parent supplies THIS node's hypotheses (the `(by assumption)`s resolve). O(1), no SMT, body- and
    combine-independent."""
    book = L.book_num(propdir)
    objs, _ = L.resolve_call_args(propdir, book, node)  # the ACTUAL object args wired (annotation or defaults)
    ok, out = _build_isolated_sp(propdir, node)
    return ok, out, objs


def check_combine(propdir, node):
    """Combine-check (CONTAINERS ONLY): build the node's backing file in its DEV state (all sub-nodes
    `:= by sorry`, the REAL combine tail) tolerating sorry. Green ⟺ the container's combine (the proof
    after its `have`s) closes the goal from the sub-node claim-TYPES — exactly what the final wired build
    feeds it. Returns ('n/a','') for a leaf (no sub-nodes ⟹ no combine), else (ok, output).
    No swap needed: the on-disk dev state already IS {sub-nodes sorry + real combine}."""
    bf = L.backing_file(propdir, node.name)
    if bf is None or not _backing_subnodes(propdir, node):
        return "n/a", ""
    ok, out = L.lake_build(L.target_of(bf), wall=L.WALL)
    return ("combine_ok" if ok else "combine_fail"), out


def _backing_subnodes(propdir, node):
    """The sub-nodes (its own `have`s) inside this node's backing file — empty ⟹ it's a leaf."""
    book = L.book_num(propdir)
    bf = L.backing_file(propdir, node.name)
    return L.parse_nodes_in_file(bf, book) if bf is not None else []


def check_provable(propdir, node):
    """P: build the node's backing file in isolation and assert ZERO sorry (LEAVES ONLY).
       status ∈ {'proven', 'fail', 'sorry', 'container'}.
       - LEAF backing file (no sub-nodes): build it isolated as-is (wall 30). 'sorry' ⟹ built green but
         a `sorry` warning remains (NOT proven).
       - CONTAINER backing file (has sub-nodes): P is SKIPPED → 'container'. A container is NOT proven by
         a build of its own; it is REDUNDANT to build (every SMT query in its wired build — each
         sub-node's hyp-discharge AND the container's combine `euclid_finish` — is already certified by
         that container's OWN sub-nodes' SP, which builds this same container file with one sub-node
         wired and the rest as sorry-claims-in-context). So container correctness = {sub-nodes' SP} +
         {sub-nodes' P, recursively} + {no stray sorry, enforced by integrity_scan}. Building the
         container here would just re-run those queries bundled under one 30s wall (the false-40s
         `step27_decomp` problem). The combine is certified by sub-node SP; leaves by P; that's complete."""
    if _backing_subnodes(propdir, node):
        return "container", ""
    bf = L.backing_file(propdir, node.name)
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
def _run_SF(propdir, node, *, site=""):
    """SF — Sufficient. Build the node's CONTAINER with the node's body as `sorry`. Returns ok.
    `site` is an optional " @ <file>" suffix used when a shared `have` is checked at multiple parents.
    NOTE on discrimination: for a `have` node, the have is USED to close its container's goal, so SF
    genuinely tests "this claim is well-typed AND closes the goal." For a MAIN SENTENCE node, Main's
    sentences are independent `have`s that don't consume each other (the final `exact`/`rw` does), so
    building Main only confirms the sentence's claim is WELL-TYPED in scope — it does NOT isolate that
    sentence's sufficiency. SP (which wires only this sentence) is the discriminating check for Main
    sentences. We say so rather than over-claim."""
    ok, out = check_sufficient(propdir, node)
    if not ok:
        print(f"FAIL (SF — sufficient{site}): {os.path.relpath(node.file, L.BOOK_ROOT)} did not build "
              f"with `{node.name}`'s claim as `sorry`. The claim is ill-typed in scope OR doesn't close "
              f"the goal it's used for (or the build hit the 30s cap). Fix the CLAIM before proving it.\n")
        print(_fail_output(out))
        return False
    if node.kind == "sentence":
        print(f"  SF ok — `{node.name}`'s claim is well-typed in Main. (Main sentences don't consume "
              f"each other, so SF only checks well-typedness here; SP isolates this sentence.)")
    else:
        print(f"  SF ok{site} — claim well-typed in {os.path.relpath(node.file, L.BOOK_ROOT)} and "
              f"sufficient (closes the goal with `{node.name}` as sorry).")
    return True


def _run_SP(propdir, node, *, site=""):
    """SP — Suppliable. Returns ok. `site` is an optional " @ <file>" suffix for multi-parent haves."""
    ok, out, objs = check_suppliable(propdir, node)
    if not ok:
        print(f"FAIL (SP — suppliable{site}): wiring "
              f"`euclid_apply ({L.helper_name(L.book_num(propdir), L.prop_num(propdir), node.name)} "
              f"{' '.join(objs)})` in {os.path.relpath(node.file, L.BOOK_ROOT)} did not build.")
        print("  → The wire FULLY applies the helper: objects positionally + one `(by assumption)` per "
              "hypothesis binder (zero SMT). SP failed for ONE of these reasons:\n"
              "    (a) a HYPOTHESIS is NOT present in the parent context → its `(by assumption)` fails "
              "(`tactic 'assumption' failed`). The signature hyp must be a fact the parent ALREADY has. "
              "FIX: remove that hyp from the helper signature and DERIVE it inside the helper body (it "
              "becomes part of the bounded ≤30s leaf build). Run `--context <node>` to see the atoms in "
              "scope;\n"
              "    (b) a hypothesis is present but in a DIFFERENT FORM/ORIENTATION than the signature asks "
              "(`assumption` is exact up to defeq — distance/angle symmetry and abbrev packaging are NOT "
              "definitional) → match the signature to the LITERAL atom the parent has (abbrevs like "
              "`formParallelogram` are unfolded to atomic conjuncts in context — take the ATOMS), or "
              "derive the reoriented fact in-body;\n"
              "    (c) an OBJECT arg name isn't in this parent's scope (`unknown identifier`) → if the "
              "helper is reused with DIFFERENT objects per parent, add a `-- @args: <objs in order>` line "
              "directly above this node to pass this site's actuals;\n"
              "    (d) the build hit the 30s cap → decompose. This is NOT a tooling wall.\n"
              "  Build output:\n")
        if "tactic 'assumption' failed" in (out or ""):
            print("  HINT: a `(by assumption)` failed above — a HYPOTHESIS binder of the helper is not "
                  f"present by type in this parent's context. Run `--context {node.name}` to see the "
                  "exact atoms in scope, then REMOVE that hyp from the signature and derive it in the "
                  "helper body (the wire discharges hyps ONLY by `assumption`; every signature hyp must "
                  "be a fact the parent has verbatim).\n")
        if node.args is None and "unknown identifier" in (out or ""):
            print("  HINT: an `unknown identifier` above means an OBJECT arg name isn't in THIS parent's "
                  "scope. If this helper is reused with DIFFERENT objects per parent, add a "
                  "`-- @args: <objs in order>` line directly above this node to pass this site's "
                  "actuals.\n")
        if "Translator] Unexpected application" in (out or ""):
            m = re.search(r"Unexpected application (\w+)", out)
            sym = m.group(1) if m else "…"
            print(f"  HINT: translator can't PROVE `{sym}` at the call site — euclid_finish was asked to "
                  f"reconstruct it. Run `--context {node.name}` to see the ACTUAL hyps in scope: if "
                  f"`{sym}` is an abbrev that's been unfolded to atomic conjuncts there, change the "
                  f"signature to take those ATOMS (which ARE in scope), not the packaged `{sym}`. "
                  f"SIGNATURE fix, NOT a cap/tooling limit.\n")
        print(_fail_output(out))
        return False
    print(f"  SP ok{site} — hyps suppliable (objects: {' '.join(objs) or '(none)'}).")
    return True


def _run_P(propdir, node, *, verbose=True):
    """P — Provable (LEAVES ONLY). Returns status ∈ {'proven','sorry','fail','container'}; prints a report."""
    status, pout = check_provable(propdir, node)
    bf_rel = os.path.relpath(L.backing_file(propdir, node.name), L.BOOK_ROOT)
    if status == "container":
        subs = _backing_subnodes(propdir, node)
        if verbose:
            print(f"  P n/a — {bf_rel} is a CONTAINER (sub-nodes: {', '.join(s.name for s in subs)}); "
                  f"not built here. Its combine is certified by its own combine-check, its sub-nodes by "
                  f"their isolated SP, its leaves by their own P. Certify those sub-nodes.")
    elif status == "fail":
        print(f"FAIL (P — provable): {bf_rel} did not build (or hit the 30s cap — decompose into more "
              f"`have`+backing files).\n")
        print(_fail_output(pout))
    elif status == "sorry":
        locs = _sorry_locations(pout)
        where = f" at {', '.join(locs)}" if locs else ""
        print(f"  P pending — {bf_rel} builds but still has `sorry`{where}. Prove it, then re-run.")
    elif verbose:
        print(f"  P ok — {bf_rel} (leaf) builds with ZERO sorry.")
    return status


def _run_combine(propdir, node, *, verbose=True):
    """Combine-check for a CONTAINER node. Returns True if the combine closes (or n/a for a leaf)."""
    status, out = check_combine(propdir, node)
    if status == "n/a":
        return True
    bf_rel = os.path.relpath(L.backing_file(propdir, node.name), L.BOOK_ROOT)
    if status == "combine_fail":
        print(f"  ✗ COMBINE FAILED — {bf_rel}'s combine (the proof after its `have`s) did not close from "
              f"the sub-node claim-types (or hit the 30s cap → factor the combine, e.g. `linarith` over "
              f"locked equalities instead of one big `euclid_finish`).\n")
        print(_fail_output(out))
        return False
    if verbose:
        print(f"  Combine ok — {bf_rel}'s combine closes from the sub-node claim-types.")
    return True


def _require_occurrences(propdir, node_name):
    """Return [Node, …] (one per call site) for node_name, or None (printing a FAIL) if unknown."""
    occs = L.parse_occurrences(propdir)
    if node_name not in occs:
        print(f"FAIL: no node '{node_name}' in {os.path.relpath(propdir, L.BOOK_ROOT)}. "
              f"Known: {', '.join(sorted(occs, key=L.natural_key))}")
        return None
    return occs[node_name]


def mode_node(propdir, node_name):
    """No-flag: run SF → SP → P in order, stopping at the first failure (the agent's default command).
    A `have` reused in several parents runs SF+SP at EVERY call site (each parent must independently
    supply it); P runs ONCE on the single backing file."""
    occs = _require_occurrences(propdir, node_name)
    if occs is None:
        return 2
    multi = len(occs) > 1
    where = f"{len(occs)} call sites" if multi else f"{occs[0].kind} in {os.path.relpath(occs[0].file, L.BOOK_ROOT)}"
    print(f"[check_step] {node_name}  ({where})")
    for nd in occs:                                   # SF + SP per call site
        site = f" @ {os.path.relpath(nd.file, L.BOOK_ROOT)}" if multi else ""
        if not _run_SF(propdir, nd, site=site):
            return 1
        if not _run_SP(propdir, nd, site=site):
            return 1
    status = _run_P(propdir, occs[0])                 # P once (leaves only; containers report 'container')
    if status == "fail":
        return 1
    if status == "sorry":
        return 0                                    # SF+SP certified; leaf body still to prove — not an error
    spx = ' ×' + str(len(occs)) if multi else ''
    if status == "container":
        if not _run_combine(propdir, occs[0]):       # a container's combine is its OWN check
            return 1
        print(f"PASS: {node_name} suppliable (SF + SP{spx}) + Combine; it's a CONTAINER — also certify "
              f"its sub-nodes (their isolated SP + their own combine/P).")
    else:
        print(f"PASS: {node_name} CERTIFIED (SF + SP{spx} + P).")
    return 0


def mode_one(propdir, node_name, which):
    """Single-flag diagnostics: --sufficient / --suppliable / --provable for one node. SF/SP run for
    every call site; P runs once."""
    occs = _require_occurrences(propdir, node_name)
    if occs is None:
        return 2
    multi = len(occs) > 1
    print(f"[check_step --{which}] {node_name}"
          f"{f' ({len(occs)} call sites)' if multi else f'  ({os.path.relpath(occs[0].file, L.BOOK_ROOT)})'}")
    if which in ("sufficient", "suppliable"):
        runner = _run_SF if which == "sufficient" else _run_SP
        for nd in occs:
            site = f" @ {os.path.relpath(nd.file, L.BOOK_ROOT)}" if multi else ""
            if not runner(propdir, nd, site=site):
                return 1
        return 0
    # provable — once
    status = _run_P(propdir, occs[0])
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
        print(_fail_output(out))
    print("\nNOTE: this is the LITERAL local context. `euclid_apply (helper…); euclid_finish` can also "
          "discharge facts NOT listed here (between/sameSide/distinctness derived by SMT). The "
          "authoritative suppliability test is SP (`check_step <node>`), not this list — do not "
          "over-decompose because something isn't shown.")
    return 0 if ok or block else 1


def _audit(propdir, order, success_msg):
    """Run a bottom-up audit over a pre-computed `order` = [(name, [occurrences]) …]: ISOLATED SP at
    every occurrence (per call site), then — per name — P (leaves, zero-sorry) OR a combine-check
    (containers). STOP at the first (deepest) failure. Shared by `--all` (order = audit_order, whole
    prop) and `--subtree` (order = subtree_order, one cone). The caller runs `integrity_scan` first
    (the no-stray-sorry + structural preamble)."""
    for name, occs in order:
        for nd in occs:
            ok, out, objs = check_suppliable(propdir, nd)
            site = f" @ {os.path.relpath(nd.file, L.BOOK_ROOT)}" if len(occs) > 1 else ""
            if not ok:
                print(f"  ✗ {name}{site}: SP FAILED (see below) — deepest failure; fix it first.\n")
                print(_fail_output(out))
                return 1
        rep = occs[0]
        status, pout = check_provable(propdir, rep)
        tag = f"{name} ({os.path.relpath(L.backing_file(propdir, name), L.BOOK_ROOT)})"
        if status == "fail":
            print(f"  ✗ {tag}: P FAILED — leaf backing file did not build (or hit the 30s cap → "
                  f"decompose).\n")
            print(_fail_output(pout))
            return 1
        if status == "sorry":
            print(f"  ✗ {tag}: P FAILED — leaf backing file builds but still has a `sorry` (unproven).\n")
            print(_fail_output(pout))
            return 1
        nsite = f" [{len(occs)} call sites]" if len(occs) > 1 else ""
        if status == "container":
            cstatus, cout = check_combine(propdir, rep)        # certify the combine on its OWN
            if cstatus == "combine_fail":
                print(f"  ✗ {tag}: COMBINE FAILED — the combine did not close from the sub-node "
                      f"claim-types (or hit the 30s cap → factor the combine).\n")
                print(_fail_output(cout))
                return 1
            print(f"  ✓ {name}: SP[isolated]{nsite} + Combine (container)")
        else:
            print(f"  ✓ {name}: SP[isolated]{nsite} + P (leaf, zero-sorry)")
    print("\n" + success_msg)
    return 0


def mode_all(propdir):
    problems = L.integrity_scan(propdir)
    if problems:
        print("FAIL (--all aborted by integrity scan — fix structure first):")
        for p in problems:
            print("  - " + p)
        return 1
    # criterion-3 dependency (source-only, instant) — enforce BEFORE the long build audit so a dep
    # violation can't slip through the agent's final gate (the step3-cited-Prop.1.31 class).
    if not _run_dependency(propdir):
        return 1
    order = L.audit_order(propdir)                    # whole prop, bottom-up
    n_names = len(order)
    n_occ = sum(len(occs) for _, occs in order)
    print(f"[check_step --all] bottom-up audit of {n_names} node(s)"
          f"{f' / {n_occ} call-site(s)' if n_occ != n_names else ''} in "
          f"{os.path.relpath(propdir, L.BOOK_ROOT)} (sub-nodes before their parents):")
    rel = os.path.relpath(propdir, L.BOOK_ROOT)
    return _audit(propdir, order,
                  f"PASS: all {n_names} node(s) certified — every leaf builds ZERO-sorry, every call "
                  f"site supplies its hyps (isolated SP, no SMT), every container's combine is certified "
                  f"by its OWN combine-check, and integrity_scan found no stray sorry ⇒ the Phase-C wired "
                  f"build is GUARANTEED green AND sorry-free. Run `python3 scripts/wire_main.py {rel}`.")


def mode_subtree(propdir, root):
    """`--subtree <node>`: audit ONLY Cone(root) (root + everything it transitively contains), bottom-up,
    occurrence-scoped to the cone. Confirms a container/step is fully done WITHOUT re-auditing the rest
    of the prop. NOT the final gate — run `--all` ONCE at the very end."""
    problems = L.integrity_scan(propdir)              # structural preamble is whole-prop, cheap, no build
    if problems:
        print("FAIL (--subtree aborted by integrity scan — fix structure first):")
        for p in problems:
            print("  - " + p)
        return 1
    order = L.subtree_order(propdir, root)            # the cone, bottom-up, scoped
    n_names = len(order)
    n_occ = sum(len(occs) for _, occs in order)
    print(f"[check_step --subtree {root}] auditing the {root} cone — {n_names} node(s)"
          f"{f' / {n_occ} in-cone call-site(s)' if n_occ != n_names else ''} in "
          f"{os.path.relpath(propdir, L.BOOK_ROOT)} (sub-nodes before {root}):")
    return _audit(propdir, order,
                  f"PASS: {root}'s subtree certified (SF/SP over every in-cone call site + P every leaf "
                  f"in the cone). This is NOT the whole prop — keep driving the remaining steps, then "
                  f"run `check_step {os.path.relpath(propdir, L.BOOK_ROOT)} --all` ONCE at the very end.")


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
        print(_fail_output(out))
        return 1
    print("OK: Main elaborates (sorry tolerated). The sentence map type-checks.")
    return 0


def _run_dependency(propdir):
    """Run the PHASE-B source-regex criterion-3 dependency check (both arms). Print problems; return ok.
    NUMBER-ONLY by design — book authentication is the HUMAN's gate-C olean check (`check_faithful.sh`).
    A citation fails iff satisfied by NEITHER the construction arm (`… as …` in Main) NOR the helper-cone
    proof arm. (Phase A — no helpers yet — uses `check_faithful.py` source mode, construction arm only.)"""
    problems = L.dependency_problems(propdir)
    if problems:
        print(f"FAIL (dependency / criterion-3): {len(problems)} cited [Prop.~B.N] not satisfied in "
              f"{os.path.relpath(propdir, L.BOOK_ROOT)} (number-only; the human's gate-C olean check is "
              f"book-aware — do NOT game this regex):")
        for p in problems:
            print("  - " + p)
        return False
    return True


def mode_dependency(propdir):
    """`--dependency`/`--deps`: ISOLATED, instant (no build) criterion-3 check (Phase-B arms). Run this to
    fast-isolate a dependency problem before the slow `--all` (which also runs it)."""
    print(f"[check_step --dependency] criterion-3 (source-regex, number-only) for "
          f"{os.path.relpath(propdir, L.BOOK_ROOT)}:")
    if not _run_dependency(propdir):
        return 1
    print("OK: every cited [Prop.~B.N] is satisfied by a Main construction (`… as …`) or its sentence's "
          "helper cone. (Book authentication is the gate-C olean check.)")
    return 0


def mode_check(propdir):
    problems = L.integrity_scan(propdir)
    if problems:
        print(f"FAIL: {len(problems)} structural problem(s) in "
              f"{os.path.relpath(propdir, L.BOOK_ROOT)}:")
        for p in problems:
            print("  - " + p)
        return 1
    # criterion-3 dependency is ALSO source-only (no build), so it belongs in the instant scan.
    if not _run_dependency(propdir):
        return 1
    n = len(L.parse_all_nodes(propdir))
    print(f"OK: {os.path.relpath(propdir, L.BOOK_ROOT)} structurally sound — {n} node(s), naming law "
          f"holds, every node has a backing file, every file carries the 30s cap, nothing pre-wired, "
          f"no stray sorry, every cited [Prop.~B.N] satisfied (construction or helper-cone).")
    return 0


# ── output helpers ────────────────────────────────────────────────────────────────────────────────
def _tail(out, n=40):
    lines = (out or "").rstrip().splitlines()
    return "\n".join(lines[-n:])


def _errors(out):
    """Extract the COMPLETE Lean `error:` blocks from a build log — each `error:` line plus all its
    continuation lines (the multi-line goal state: `unsolved goals`, `linarith failed`, the `⊢ …`,
    `unknown … `, the `[Smt.Translator] …` note, etc.) up to the next `error:`/`warning:`/`info:` or a
    lake status line. This gives the agent the ACTUAL diagnosis (e.g. 'linarith failed / unsolved
    goals: <state>' vs 'unknown tactic linear_combination') without reading `.lake` logs by hand."""
    lines = (out or "").splitlines()
    boundary = re.compile(r"^(error:|warning:|info:|trace:|✔|✖|ℹ|⚠|Build completed|Some builds|\[\d)")
    blocks, i, n = [], 0, len(lines)
    while i < n:
        if lines[i].startswith("error:"):
            blk = [lines[i]]; i += 1
            while i < n and not boundary.match(lines[i]):
                blk.append(lines[i]); i += 1
            blocks.append("\n".join(blk).rstrip())
        else:
            i += 1
    return "\n\n".join(blocks)


def _fail_output(out):
    """What to print on a build failure: the full `error:` blocks if any (the real diagnosis), else the
    tail (e.g. a wall-timeout message that isn't an `error:` line)."""
    errs = _errors(out)
    return errs if errs.strip() else _tail(out)


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

        # `--check` is pure source-read (no swap) → no lock needed. Every OTHER mode mutates files
        # (swap→build→revert), so it runs under the PER-PROP lock: one runner at a time per prop, so two
        # concurrent runs on the same prop can't clobber each other's edits. Different props parallelize.
        if rest == ["--check"]:
            return mode_check(propdir)
        if rest in (["--dependency"], ["--deps"]):   # source-only (no build/swap) → no lock needed
            return mode_dependency(propdir)
        if rest in (["--sufficient"], ["--suppliable"]):
            abbr = "SF" if rest[0] == "--sufficient" else "SP"
            print(f"FAIL: `{rest[0]}` needs a NODE argument (e.g. `{rest[0]} step5`). "
                  f"{abbr} is a per-node check; Main has no parent so it has no SF/SP — use "
                  f"`--provable` with no node to build Main.")
            return 2
        if rest == ["--subtree"]:
            print("FAIL: `--subtree` needs a NODE argument (e.g. `--subtree step27`) — it audits that "
                  "node's cone. To audit the WHOLE prop, use `--all` (the final gate, run ONCE).")
            return 2

        def dispatch():
            if rest == ["--all"]:
                return mode_all(propdir)
            if rest == ["--provable"]:               # no node = Phase-A: build Main, tolerate sorry
                return mode_build_main(propdir)
            if len(rest) == 2 and rest[0] == "--subtree":
                return 2 if reject_main_as_node(rest[1]) else mode_subtree(propdir, as_node(rest[1]))
            if len(rest) == 2 and rest[0] == "--context":
                return 2 if reject_main_as_node(rest[1]) else mode_context(propdir, as_node(rest[1]))
            if len(rest) == 2 and rest[0] in ("--sufficient", "--suppliable", "--provable"):
                return 2 if reject_main_as_node(rest[1]) else mode_one(propdir, as_node(rest[1]), rest[0][2:])
            if len(rest) == 1 and not rest[0].startswith("-"):
                return 2 if reject_main_as_node(rest[0]) else mode_node(propdir, as_node(rest[0]))
            print(__doc__)
            return 2

        with L.prop_lock(propdir):                   # serialize same-prop runs (different props parallel)
            return dispatch()
    except L.FaithfulError as e:
        print(f"ABORT (structural/naming error — refusing to proceed): {e}")
        return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
