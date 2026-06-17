#!/usr/bin/env python3
"""SMT FAILURE-CASE PROBE — build the "should-close-but-times-out" catalog (see SMTFailures/README.md).

Book-2 Euclid sentences were proven by HEAVILY decomposing each sentence into many small backing
`step` files because the SMT backend (`euclid_finish`, a z3+cvc5 portfolio) TIMES OUT on the whole-
sentence goal — even though the goal IS entailed by the helper's hypotheses + the System E SMT theory.
That manual decomposition is exactly what a strong SMT solver "should" do on its own.

For each certified node this tool captures TWO-SIDED evidence:
  NEGATIVE — synthesize a "naive" file (the helper signature, body = `euclid_intros; euclid_finish`)
             and build it at each cap. It TIMES OUT (wall-kill) or the solver gives up ("Could not
             prove" = unknown). With `--trace` we dump the exact SMT-LIBv2 query (`systemE.trace`).
  POSITIVE — the goal IS provable (the certified decomposition exists), and with `--probe-substeps`
             each sub-step's monolithic query closes FAST (<1s). So it's a solver weakness, not an
             unprovable / counterexample-bearing goal.

CLASSIFICATION (from the decomposition's source — the node's whole cone):
  A — goal-size failure : the decomposition only CHOPS the goal into smaller euclid_finish-closed
      sub-goals; introduces NO new objects, cites NO lemmas. Strongest "solver should close it" claim.
  B — trigger/instantiation failure (the deeper one) : the decomposition hand-instantiates an axiom
      that IS in the SMT theory (e.g. `rectangle_area`, `parallelogram_area`) — the solver could have
      e-matched it but its triggers never fired. The entry records WHICH axiom unblocked it.
  C — genuine construction → EXCLUDED (not a failure): introduces a witness via `euclid_apply (…) as x`
      or a lemma absent from the SMT theory (Book2/Helpers lemmas, `proposition_N`, pasch). The witness
      is NOT in the helper signature, so the monolith is NOT entailed — the solver can't be blamed.
  REVIEW — the scanner can't classify confidently (logged for a human, never auto-cataloged).

USAGE  (run BARE from LeanEuclidPlus/ — no cd, no pipe):
  python3 scripts/smt_probe.py <propdir> <node> [opts]        probe one node
  python3 scripts/smt_probe.py <propdir> --all-nodes [opts]   probe every certified node in the prop
  python3 scripts/smt_probe.py <propdir> --classify-only <node>   A/B/C verdict + evidence, NO build
  python3 scripts/smt_probe.py --emit-catalog <out_dir> <props…>  assemble SMTFailures/ from probes
opts:
  --caps 30,300        comma list of solver caps (seconds), probed in order (default 30,300)
  --wall-pad 30        wall = cap + pad seconds for the kill (default 30)
  --no-trace           do NOT set `systemE.trace true` / don't capture the .smt2 query (default: capture)
  --probe-substeps     ALSO probe each sub-node's monolith (the "N small queries each <1s" contrast)
  --max-budget <s>     stop launching new probes once cumulative build wall-time exceeds this
  --reprobe            ignore the cache and re-probe every node (force a fresh build)
  --json               machine-readable result(s) to stdout (one dump at the end)
  --jsonl <file>       STREAM one record per node to <file> as each completes (append+flush, so a
                       scancel mid-run leaves a valid partial file; tail-able; load with
                       `pd.read_json(<file>, lines=True)` or DuckDB `SELECT * FROM '<file>'`).
  --clean              remove any stray `_probe_*.lean` left by an interrupted run, then exit

CACHING: `--all-nodes` caches each node's probe result under .lake/smt-probe-cache/ (git-ignored),
keyed by the node's CONE HASH (its backing file + sub-files) and a global EPOCH (the SMT theory file +
caps + toolchain). A re-run RE-PROBES only nodes whose source changed (or new ones) and reuses the rest
instantly — so adding a prop or editing a proof costs only the affected nodes. Changing the SMT theory
or caps invalidates the whole cache (the verdict could differ). Use `--reprobe` to force a clean rebuild.

NOTE: a node is a CATALOG CANDIDATE iff its naive build times out at the LARGEST cap, its
decomposition is CERTIFIED (in the prop's .lake/faithful-certified manifest), and it classifies A or B.
"""
import os, re, sys, time, json, glob
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))   # so `faithful_lib` resolves from any cwd
import faithful_lib as L


# ── name sets distinguishing B (in-theory axiom) from C (construction / theory-absent lemma) ──────────
THEORY_FILE = os.path.join(L.BOOK_ROOT, "SystemE", "Meta", "Smt", "EuclidTheory.lean")
INFERENCES_DIR = os.path.join(L.BOOK_ROOT, "SystemE", "Theory", "Inferences")
HELPERS_DIR = os.path.join(L.BOOK_ROOT, "Book2", "Helpers")

# A `-- <label>` line on its own in EuclidTheory.lean names an SMT-LIB axiom that IS in the query the
# solver receives. Hand-instantiating one of these is a B (trigger-miss) case, not a missing fact.
_THEORY_LABEL_RE = re.compile(r"^\s*--\s*([a-z][a-z0-9_]*)\s*$", re.MULTILINE)
_AXIOM_RE = re.compile(r"\baxiom\s+(\w+)")
_DECL_RE = re.compile(r"\b(?:theorem|lemma|def)\s+(\w+)")


def _read(path):
    try:
        with open(path, encoding="utf-8") as f:
            return f.read()
    except OSError:
        return ""


def smt_theory_names():
    """The set of axiom names the SMT background theory actually contains (its `-- label` comments).
    `rectangle_area`/`parallelogram_area`/`sum_parallelograms_area`/`congruent_*`/… are here; pasch is
    NOT (it's a Lean-only inference axiom). Membership here is the B-vs-C boundary."""
    return set(_THEORY_LABEL_RE.findall(_read(THEORY_FILE)))


def lean_axiom_names():
    """Lean `axiom …` names under SystemE/Theory/Inferences (pasch_*, transfer axioms, …). Some (e.g.
    rectangle_area) ALSO appear in the SMT theory; those are B. A Lean axiom NOT in the SMT theory
    (pasch) means the monolith can't derive it ⟹ exclude."""
    names = set()
    for p in glob.glob(os.path.join(INFERENCES_DIR, "**", "*.lean"), recursive=True):
        names.update(_AXIOM_RE.findall(_read(p)))
    return names


def helper_lemma_names():
    """Book2/Helpers lemma/def names (mk_parallelogram, sameSide_of_parallel, offLine_of_parallel, …).
    These are Lean reasoning the SMT theory lacks ⟹ using one is a C (construction) exclusion."""
    names = set()
    for p in glob.glob(os.path.join(HELPERS_DIR, "**", "*.lean"), recursive=True):
        names.update(_DECL_RE.findall(_read(p)))
    return names


# computed once on first use
_NAMESETS = {}


def _namesets():
    if not _NAMESETS:
        _NAMESETS["theory"] = smt_theory_names()
        _NAMESETS["axioms"] = lean_axiom_names()
        _NAMESETS["helpers"] = helper_lemma_names()
    return _NAMESETS


# ── classifier ────────────────────────────────────────────────────────────────────────────────────
# A head identifier applied in the body — captured from `euclid_apply (HEAD …)` and term-mode
# `have NAME [: T] := HEAD …` (NOT `:= by …`). euclid_apply heads are always lemma/axiom/construction
# names (never tactics), so no tactic ignore-list is needed for them.
_HAVE_TERM_RE = re.compile(r"\bhave\b[^:=]*?:=\s*(?!by\b)([A-Za-z_]\w*)")


def _head_ident(term):
    """First identifier token of an `euclid_apply` inner term, e.g. 'rectangle_area c b l m' → 'rectangle_area'."""
    m = re.match(r"\s*([A-Za-z_]\w*)", term)
    return m.group(1) if m else None


# A witness introduced by a route OTHER than `euclid_apply (…) as` — which the probe synthesis does NOT
# preserve, so the naive build would silently drop the object and the A/B tag would be unsound. The
# faithful pipeline forbids these in backing files (every object is constructed in Main and passed as a
# signature parameter), so today there are ZERO; this guard ENFORCES that invariant rather than trusting
# it, flagging any future violator REVIEW instead of mis-tagging it a clean SMT-failure case.
#
# IMPORTANT: a bare `obtain ⟨…⟩ := <localName>` is NOT a witness — it just DESTRUCTURES an already-proven
# conjunction `have` into its named Prop conjuncts (ubiquitous in these proofs, e.g. step5's
# `obtain ⟨hbc,…⟩ := step5_dist`, all benign). A real object-introducing `obtain` binds from a CALL that
# produces an existential — `obtain ⟨x, hx⟩ := euclid_… ` — so we match only `obtain … := euclid_`, plus
# explicit `∃` / `exists.intro` / a `let`-bound object. (Verified: zero such forms across Prop01-04.)
WITNESS_RE = re.compile(
    r"\bobtain\b[^\n]*:=\s*euclid_"       # obtain … := euclid_apply/euclid_… (binds from a CALL, not a have)
    r"|\bexists\.intro\b|\b∃\b"           # explicit existential introduction
    r"|^\s*let\b",                        # a let-bound (possibly object) definition
    re.MULTILINE)


def classify_node(propdir, node):
    """Tag `node` 'A' | 'B' | 'REVIEW' from its OWN body (the decomposition the probe strips). EVERY node
    is still probed — this only labels HOW the human's body departed from a one-shot, so a timeout's
    catalog entry tells the SMT team which failure mode it is:
      B — the body hand-instantiates an axiom that IS in the SMT theory (rectangle_area, pasch_*, …):
          the solver had it but its triggers never fired (the deeper miss). Records which axiom.
      A — the body only splits the goal into euclid_finish-closed `have`s (+ maybe `as` constructions,
          which the probe KEEPS). Pure goal-size pressure.
      REVIEW — the body introduces a witness by a non-`as` route (obtain / ∃-elim / let / `:= ⟨…⟩`) that
          the probe synthesis does NOT preserve. Then "construction-free" would be FALSE and the A/B
          claim unsound, so it's flagged for a human (never silently counted). The pipeline forbids these
          in backing files, so this fires only if that invariant is ever broken (future prop / hand-edit).
    `as` constructions ARE kept in the probe, so they only get noted, not flagged. Scans only the node's
    own backing-file body (NOT the cone: sub-files are probed as their own nodes). Returns (tag, evidence)."""
    ns = _namesets()
    theory = ns["theory"]
    bf = L.backing_file(propdir, node)
    if bf is None:
        return "A", ["(no backing file)"]
    assign, body_end = _theorem_body_span(_read(bf))
    body = L.blank_comments(_read(bf)[assign:body_end])
    evidence, b_axioms, constructions = [], set(), 0
    # (0) unsound-for-the-probe witness introductions → REVIEW (the probe can't preserve these)
    wm = WITNESS_RE.search(body)
    if wm:
        tok = body[wm.start():wm.end()].strip() or body[wm.start():body.find(chr(10), wm.start())].strip()
        return "REVIEW", [f"body introduces a witness via `{tok}` (not `euclid_apply … as`) — the probe "
                          f"can't preserve it, so 'construction-free' is unverified. HUMAN-REVIEW this "
                          f"node before trusting its tag (the faithful pipeline normally forbids this)."]
    for m in L.APPLY_AS_RE.finditer(body):            # kept constructions — note, don't gate
        constructions += 1
        head = _head_ident(m.group(1)) or "?"
        evidence.append(f"keeps construction `{head} … as` (probe retains it)")
    # bare applications + term-mode `have := head …`: a head in the SMT theory ⟹ B signal
    heads = [_head_ident(m.group(1)) for m in L.APPLY_NOAS_RE.finditer(body)]
    heads += [m.group(1) for m in _HAVE_TERM_RE.finditer(body)]
    for head in heads:
        if not head or head.startswith("helper_"):     # internal wiring to a sub-node — ignore
            continue
        if head.rstrip("'") in theory or head in theory:
            b_axioms.add(head)
            evidence.append(f"hand-instantiates in-theory axiom `{head}` (B trigger-miss)")
    if b_axioms:
        return "B", evidence
    return "A", evidence or ["(body only splits the goal into euclid_finish-closed steps — pure A)"]


def instantiated_axioms(propdir, node):
    """The SMT-theory axiom names the node's OWN body hand-instantiates (the B trigger hint). Empty for A."""
    ns = _namesets()
    theory = ns["theory"]
    bf = L.backing_file(propdir, node)
    if bf is None:
        return []
    assign, body_end = _theorem_body_span(_read(bf))
    src = L.blank_comments(_read(bf)[assign:body_end])
    found = set()
    for m in L.APPLY_NOAS_RE.finditer(src):
        head = _head_ident(m.group(1))
        if head and not head.startswith("helper_") and (head.rstrip("'") in theory or head in theory):
            found.add(head)
    for m in _HAVE_TERM_RE.finditer(src):
        head = m.group(1)
        if not head.startswith("helper_") and (head.rstrip("'") in theory or head in theory):
            found.add(head)
    return sorted(found)


# ── naive-file synthesis ──────────────────────────────────────────────────────────────────────────
def extract_constructions(body):
    """Return the list of full `euclid_apply (<term>) as <idents>` statements in `body`, in source order.
    These INTRODUCE new objects (points/lines the solver cannot invent), so the naive probe MUST keep
    them — only the derived `have`s and bare fact-applications are stripped. Uses balanced-paren matching
    on a comment-blanked copy (so the term's own nested parens and commented code are handled). The `as`
    clause is captured to end-of-line (`as f` or `as ⟨h1, h2⟩` / `as (AB CD)`)."""
    clean = L.blank_comments(body)
    out = []
    for m in re.finditer(r"euclid_apply\s*\(", clean):
        close = L.balanced_paren(clean, m.end())          # matching `)` of the term
        tail = clean[close + 1:]
        am = re.match(r"\s*as\b", tail)
        if not am:
            continue                                      # not a construction (no `as`) — skip
        eol = clean.find("\n", close + 1)
        stmt_end = eol if eol != -1 else len(clean)
        out.append(body[m.start():stmt_end].strip())      # the ORIGINAL (un-blanked) text
    return out


def _theorem_body_span(src):
    """Return (assign, body_end): the index of the theorem's top-level `:=` and the end of its proof
    (the namespace `end`/EOF, comment-blanked)."""
    m = re.search(r"^theorem\s", src, re.MULTILINE)
    if not m:
        raise L.FaithfulError("smt_probe: no top-level `theorem` in backing file")
    depth, i, n, assign = 0, m.end(), len(src), None
    while i < n:
        c = src[i]
        if c == '"':
            i = L._skip_string(src, i, n); continue
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif depth == 0 and src.startswith(":=", i):
            assign = i; break
        i += 1
    if assign is None:
        raise L.FaithfulError("smt_probe: no top-level `:=` for the theorem")
    clean = L.blank_comments(src)
    em = re.search(r"^end\b", clean[assign:], re.MULTILINE)
    body_end = assign + em.start() if em else len(src)
    return assign, body_end


def _set_theorem_probe_body(src):
    """Replace the file's top-level theorem proof with the NAIVE probe body: `euclid_intros`, then every
    `euclid_apply (...) as …` CONSTRUCTION from the original body kept VERBATIM (the solver can't invent
    those objects), then a single `euclid_finish`. The human's derived `have`s and bare fact-applications
    are dropped — the probe asks whether `euclid_finish` re-derives the whole goal in one shot given only
    the constructed objects. (A body with no `as` reduces to `euclid_intros; euclid_finish`.)"""
    assign, body_end = _theorem_body_span(src)
    constructions = extract_constructions(src[assign:body_end])
    lines = ["  euclid_intros"] + ["  " + c for c in constructions] + ["  euclid_finish"]
    probe = ":= by\n" + "\n".join(lines) + "\n\n"
    return src[:assign] + probe + src[body_end:], len(constructions)


def synth_probe_src(propdir, node, cap, trace):
    """Synthesize the standalone naive probe source for `node`: its backing file's verbatim signature,
    body replaced by the naive probe tactic (euclid_intros + kept `as` constructions + euclid_finish),
    pipeline imports dropped, the chosen solver cap (+ optional trace) set above the theorem.
    Returns (probe_src, backing_file_path, n_constructions)."""
    bf = L.backing_file(propdir, node)
    if bf is None:
        raise L.FaithfulError(f"node '{node}' has no backing file '{node}.lean'")
    src = _read(bf)
    for mod in L.pipeline_imports(src, propdir):       # drop helper/step imports — naive file has no decomposition
        src = L.remove_import(src, mod)
    src = L.strip_caps(src)                             # remove the dev 30s cap; we set our own
    src, n_cons = _set_theorem_probe_body(src)
    opts = f"set_option systemE.solverTime {cap} in\n"
    if trace:
        opts += "set_option systemE.trace true in\n"
    m = re.search(r"^theorem\s", src, re.MULTILINE)
    if m is None:
        raise L.FaithfulError(f"smt_probe: no top-level `theorem` in {os.path.relpath(bf, L.BOOK_ROOT)}")
    src = src[:m.start()] + opts + src[m.start():]
    return src, bf, n_cons


def _probe_path(bf):
    """The throwaway probe file path beside the backing file: `<dir>/_probe_<node>.lean`."""
    d, base = os.path.dirname(bf), os.path.basename(bf)
    return os.path.join(d, "_probe_" + base)


def _imports_of(src):
    return [m.group(1) for m in re.finditer(r"^[ \t]*import[ \t]+(\S+)", src, re.MULTILINE)]


# ── build + status ──────────────────────────────────────────────────────────────────────────────────
def _status(ok, out):
    """Classify a probe build outcome:
       'pass'          — solved (built green, no sorry);
       'wall_timeout'  — the WALL killed it (faithful_lib's "exceeded …s wall clock");
       'solver_timeout'— euclid_finish gave up (solver returned unknown → "Could not prove");
       'error'         — a real Lean/translator error (the synthesized file is malformed → not a datapoint).
    wall_timeout and solver_timeout are both the should-close-but-didn't FAILURE evidence we catalog."""
    if ok and not L.has_sorry(out):
        return "pass"
    if "exceeded" in (out or "") and "wall clock" in (out or ""):
        return "wall_timeout"
    if "Could not prove" in (out or ""):
        return "solver_timeout"
    return "error"


def _extract_query(out, probe_base):
    """Pull the dumped SMT-LIBv2 query from a `--trace` build log. `systemE.trace true` makes evalSmt
    logInfo the whole query (theory ++ context, ending `(check-sat)`); it lands as an `info:
    <probefile>:line:col:` block. Return the query text (the block that contains `(check-sat)`), or ''."""
    lines = (out or "").splitlines()
    info_re = re.compile(r"^info: .*:\d+:\d+:")
    boundary = re.compile(r"^(info:|error:|warning:|trace:|✔|✖|ℹ|⚠|Build completed|Some builds|\[\d)")
    i, n = 0, len(lines)
    blocks = []
    while i < n:
        if info_re.match(lines[i]) and probe_base in lines[i]:
            first = re.sub(r"^info: .*?:\d+:\d+:\s*", "", lines[i])
            blk = [first] if first.strip() else []
            i += 1
            while i < n and not boundary.match(lines[i]):
                blk.append(lines[i]); i += 1
            blocks.append("\n".join(blk).strip())
        else:
            i += 1
    for b in blocks:
        if "(check-sat)" in b or "declare-sort" in b:
            return b
    return ""


def probe_build(propdir, node, cap, *, wall_pad, trace):
    """Build ONE naive probe of `node` at solver cap `cap`. Writes `_probe_<node>.lean`, warms deps,
    builds (walled at cap+pad), captures status/elapsed and (if trace) the .smt2 query. Always removes
    the probe file + invalidates its artifact, even on interrupt. Returns a dict."""
    src, bf, _ = synth_probe_src(propdir, node, cap, trace)
    pp = _probe_path(bf)
    target = L.target_of(pp)
    probe_base = os.path.basename(pp)
    with L.prop_lock(propdir):                          # serialize with any check_step on this prop
        try:
            with open(pp, "w", encoding="utf-8") as f:
                f.write(src)
            for mod in _imports_of(src):                # warm deps so the timed build measures only the SMT call
                L.warm_build(mod)
            wall = cap + wall_pad
            t0 = time.monotonic()
            ok, out = L.lake_build(target, wall=wall)
            elapsed = time.monotonic() - t0
        finally:
            try:
                os.unlink(pp)
            except OSError:
                pass
            L._invalidate_target(target)
    status = _status(ok, out)
    rec = {"cap_s": cap, "status": status, "elapsed_s": round(elapsed, 1)}
    query = _extract_query(out, probe_base) if trace else ""
    if status == "error":
        rec["error_tail"] = "\n".join((out or "").splitlines()[-15:])
    return rec, query


def probe_node(propdir, node, *, caps, wall_pad, trace, probe_substeps):
    """Probe `node` across `caps` (escalating): if it PASSES at a cap it's not a failure → stop early.
    Returns a result dict with the classification, per-cap monolith timings, the captured query, and
    (optionally) each sub-step's fast-close timing."""
    book = L.book_num(propdir)
    prop = L.prop_num(propdir)
    cat, evidence = classify_node(propdir, node)
    bf = L.backing_file(propdir, node)
    if bf is not None:
        L.parse_helper_objs(bf, book, node)            # validates the naming law (raises if violated)
    claim = _backing_claim(bf) if bf else ""
    result = {
        "id": f"Book{book}_Prop{prop}_{node}",
        "book": book, "prop": prop, "node": node,
        "helper": L.helper_name(book, prop, node),
        "failure_mode": cat,
        "evidence": evidence,
        "instantiated_axiom": instantiated_axioms(propdir, node) if cat == "B" else [],
        "goal": claim,
        "decomposition": _decomposition_info(propdir, node),
        "certified": _is_certified(propdir, node),
        "monolithic": [],
        "query": "",
        "substeps": [],
    }
    query = ""
    for cap in caps:
        rec, q = probe_build(propdir, node, cap, wall_pad=wall_pad, trace=trace)
        result["monolithic"].append(rec)
        if q and not query:
            query = q
        if rec["status"] == "pass":
            break                                       # closes at this cap ⟹ NOT a failure; don't escalate
    result["query"] = query
    if probe_substeps and _is_failure(result):
        for sub in sorted(L.cone_names(propdir, node) - {node}, key=L.natural_key):
            if L.backing_file(propdir, sub) is None:
                continue
            try:
                rec, _ = probe_build(propdir, sub, caps[0], wall_pad=wall_pad, trace=False)
            except L.FaithfulError:
                continue
            result["substeps"].append({"node": sub, **{k: rec[k] for k in ("status", "elapsed_s")}})
    return result


def _is_failure(result):
    """True iff the monolith never passed (every probed cap timed out / solver gave up)."""
    return result["monolithic"] and all(m["status"] in ("wall_timeout", "solver_timeout")
                                         for m in result["monolithic"])


def _backing_claim(bf):
    """The result type of a backing theorem (text between its top-level `:` after binders and `:=`)."""
    src = _read(bf)
    m = re.search(r"^theorem\s+helper_\w+", src, re.MULTILINE)
    if not m:
        return ""
    # walk binders to the result-type colon, then to `:=`
    i, n, depth = m.end(), len(src), 0
    while i < n:
        c = src[i]
        if c == '"':
            i = L._skip_string(src, i, n); continue
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif depth == 0 and c == ":":
            try:
                claim, _ = L.type_until_assign(src, i + 1)
                return " ".join(claim.split())
            except L.FaithfulError:
                return ""
        i += 1
    return ""


def _decomposition_info(propdir, node):
    bf = L.backing_file(propdir, node)
    cone = sorted(L.cone_names(propdir, node) - {node}, key=L.natural_key)
    cone_files = []
    for n in cone:
        cbf = L.backing_file(propdir, n)
        if cbf is not None:
            cone_files.append(os.path.relpath(cbf, L.BOOK_ROOT))
    book = L.book_num(propdir)
    n_sub = len(L.parse_nodes_in_file(bf, book)) if bf else 0
    return {
        "backing_file": os.path.relpath(bf, L.BOOK_ROOT) if bf else None,
        "cone_files": cone_files,
        "n_subnodes": n_sub,
    }


def _is_certified(propdir, node):
    return node in L.read_manifest(propdir).get("certified", {})


# ── catalog assembly ──────────────────────────────────────────────────────────────────────────────
def _git_rev():
    try:
        import subprocess
        return subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=L.BOOK_ROOT,
                                       text=True).strip()
    except Exception:
        return ""


def _toolchain():
    return _read(os.path.join(os.path.dirname(L.BOOK_ROOT), "lean-toolchain")).strip() or \
           _read(os.path.join(L.BOOK_ROOT, "lean-toolchain")).strip()


# ── probe cache (skip re-probing unchanged nodes; auto-invalidate on edit / theory change) ────────────
# A git-ignored sidecar under .lake/, mirroring check_step's certification manifest. Each node's cached
# probe result stays valid iff (a) the GLOBAL EPOCH is unchanged — the SMT theory file + the solver caps
# + the lean toolchain (anything that would change the solver's verdict), and (b) the node's CONE HASH is
# unchanged — the bytes of every backing file in the node's cone (so editing the proof, the signature, or
# any sub-file re-probes that node automatically). No transitive cascade beyond the cone, exactly like
# check_step. So `--all-nodes` re-probes ONLY new/edited nodes; adding a new prop later just appends.
import hashlib


def _epoch(caps):
    """A signature of everything global that could change a probe verdict: the SMT theory file bytes, the
    solver caps probed, the lean toolchain, AND THIS SCRIPT'S OWN BYTES. If any changes, every cached
    result is invalidated — so editing smt_probe.py (e.g. the body-synthesis logic) auto-discards stale
    results, and a plain `sbatch` is always correct (no `--reprobe` needed after a code change)."""
    h = hashlib.sha256()
    h.update((L.file_sha(THEORY_FILE) or "").encode())
    h.update(("caps=" + ",".join(map(str, caps))).encode())
    h.update(("tc=" + _toolchain()).encode())
    h.update((L.file_sha(os.path.abspath(__file__)) or "").encode())   # the probe logic itself
    return h.hexdigest()


def _cone_hash(propdir, node):
    """sha256 over the bytes of every backing file in `node`'s cone (the node + its transitive sub-files).
    Any edit to the node's signature, proof, or a sub-file changes this ⟹ the node re-probes."""
    h = hashlib.sha256()
    for name in sorted(L.cone_names(propdir, node), key=L.natural_key):
        bf = L.backing_file(propdir, name)
        h.update(name.encode())
        h.update((L.file_sha(bf) or "").encode() if bf else b"")
    return h.hexdigest()


def cache_path(propdir):
    key = os.path.relpath(propdir, L.BOOK_ROOT).replace(os.sep, "_")
    d = os.path.join(L.BOOK_ROOT, ".lake", "smt-probe-cache")
    os.makedirs(d, exist_ok=True)
    return os.path.join(d, f"{key}.json")


def read_cache(propdir, caps):
    """Load this prop's probe cache, but ONLY the slice matching the current epoch (else return empty —
    a theory/toolchain/caps change correctly invalidates everything). Returns {node: {cone_hash, result}}."""
    p = cache_path(propdir)
    if not os.path.exists(p):
        return {}
    try:
        with open(p, encoding="utf-8") as f:
            data = json.load(f)
    except (ValueError, OSError):
        return {}
    if data.get("epoch") != _epoch(caps):
        return {}
    return data.get("nodes", {})


def write_cache(propdir, caps, nodes):
    """Persist the cache (atomic-ish). Stamps the current epoch alongside the node results."""
    p = cache_path(propdir)
    tmp = p + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump({"epoch": _epoch(caps), "nodes": nodes}, f, indent=2)
    os.replace(tmp, p)


def flat_record(res):
    """One analysis-friendly JSONL record per node: the headline scalars promoted to top level (so a
    `pd.read_json(lines=True)` / DuckDB load needs no unnesting for the common queries), with the nested
    per-cap timings and lists kept alongside. `verdict`/`elapsed_s`/`cap_s` come from the LAST probed cap
    (the decisive one — a node that passed earlier stops there; one that timed out at every cap reports
    the largest)."""
    mono = res.get("monolithic", [])
    last = mono[-1] if mono else {}
    return {
        "id": res["id"],
        "book": res["book"], "prop": res["prop"], "node": res["node"],
        "failure_mode": res["failure_mode"],            # A | B
        "verdict": last.get("status", "n/a"),           # pass | wall_timeout | solver_timeout | error
        "is_failure": _is_failure(res),                 # the headline: did the monolith never close?
        "elapsed_s": last.get("elapsed_s"),
        "cap_s": last.get("cap_s"),
        "instantiated_axiom": res.get("instantiated_axiom", []),
        "n_subnodes": res.get("decomposition", {}).get("n_subnodes", 0),
        "certified": res.get("certified", False),
        "goal": res.get("goal", ""),
        "monolithic": mono,                             # full per-cap list, kept for deeper analysis
        "substeps": res.get("substeps", []),
    }


def write_entry(out_dir, result, query):
    """Write one catalog entry folder under out_dir/<A|B>/<id>/ and return its relative path (or None
    if the node isn't a failure / isn't A|B)."""
    cat = result["failure_mode"]
    if cat not in ("A", "B") or not _is_failure(result):
        return None
    entry_rel = os.path.join(cat, result["id"])
    entry_dir = os.path.join(out_dir, entry_rel)
    os.makedirs(entry_dir, exist_ok=True)
    # naive.lean — regenerate at the largest cap, with trace, for a faithful reproduction artifact
    propdir = os.path.join(L.BOOK_ROOT, result["decomposition"]["backing_file"].rsplit("/", 1)[0])
    big_cap = max(m["cap_s"] for m in result["monolithic"])
    naive_src, _, _ = synth_probe_src(propdir, result["node"], big_cap, True)
    with open(os.path.join(entry_dir, "naive.lean"), "w", encoding="utf-8") as f:
        f.write(naive_src)
    if query:
        with open(os.path.join(entry_dir, "query.smt2"), "w", encoding="utf-8") as f:
            f.write(query + ("\n(check-sat)\n" if "(check-sat)" not in query else "\n"))
        result["smt_query"] = os.path.join(entry_rel, "query.smt2")
    result["naive_lean"] = os.path.join(entry_rel, "naive.lean")
    # decomposition.md — the pointer to the working proof
    d = result["decomposition"]
    md = [f"# {result['id']} — working decomposition\n",
          f"**Goal:** `{result['goal']}`\n",
          f"**Failure mode:** {cat}" + (f" (instantiates `{', '.join(result['instantiated_axiom'])}`)"
                                        if result["instantiated_axiom"] else "") + "\n",
          f"**Backing file:** [{d['backing_file']}](../../../{d['backing_file']})  "
          f"({d['n_subnodes']} sub-node(s))\n", "**Cone files:**\n"]
    md += [f"- [{c}](../../../{c})" for c in d["cone_files"]] or ["- (leaf — no sub-files)"]
    with open(os.path.join(entry_dir, "decomposition.md"), "w", encoding="utf-8") as f:
        f.write("\n".join(md) + "\n")
    # substeps
    if result["substeps"]:
        sd = os.path.join(entry_dir, "substeps")
        os.makedirs(sd, exist_ok=True)
        with open(os.path.join(sd, "timings.json"), "w", encoding="utf-8") as f:
            json.dump(result["substeps"], f, indent=2)
    # entry.json — self-contained copy
    with open(os.path.join(entry_dir, "entry.json"), "w", encoding="utf-8") as f:
        json.dump(result, f, indent=2)
    return entry_rel


CATALOG_README = """\
# SMT Failure-Case Catalog

Generated by `scripts/smt_probe.py`. Each entry is a Euclid sentence whose **monolithic** SMT query
(`euclid_intros; euclid_finish` over the helper's exact signature) **times out**, even though the goal
**is** entailed by the System E SMT theory + the signature's hypotheses — proven by the certified
decomposition the entry points to. This is a benchmark suite of *should-close-but-hangs* queries for
SMT-solver researchers.

## Layout
- `catalog.json` — machine-readable index of every entry (A and B).
- `A/<id>/` — **goal-size failures**: the decomposition only splits the goal into smaller
  `euclid_finish`-closed pieces (no new objects, no lemma citations). The solver had everything; it
  just couldn't handle the monolithic query.
- `B/<id>/` — **trigger/instantiation failures** (the deeper miss): the decomposition hand-instantiates
  an axiom that **is already in the SMT theory** (recorded in `instantiated_axiom`); the solver could
  have e-matched it but its triggers never fired. The human had to reason about the figure's axioms by
  hand.

Each `<id>/` holds: `naive.lean` (the one-shot file), `query.smt2` (the dumped SMT-LIBv2 query — stored
once; the cap is a solver flag, not part of the query), `decomposition.md` (pointer to the working
proof), `substeps/` (each sub-step's monolith closes in <1s — the "feed it the pieces and it works"
contrast), and `entry.json`.

## Excluded (NOT failures)
Nodes whose decomposition introduces a **new witness** (`euclid_apply (…) as x`) or cites a lemma
**absent** from the SMT theory (Book2/Helpers lemmas, `proposition_N`, `pasch_*`) are excluded: the
witness isn't in the signature, so the monolith genuinely isn't entailed — not a solver weakness.

## Reproduce one entry
```
python3 scripts/smt_probe.py <propdir> <node> --caps 30,300 --probe-substeps
```
"""


def emit_catalog(out_dir, props, *, caps, wall_pad, probe_substeps, max_budget, reprobe=False):
    """Probe every certified node across `props`, classify, and assemble the catalog at out_dir. Reuses
    the per-prop probe cache (so re-emitting after adding a prop only probes the new nodes)."""
    out_dir = os.path.abspath(out_dir)
    os.makedirs(out_dir, exist_ok=True)
    entries, spent = [], 0.0
    for prop in props:
        propdir = L.propdir_of(prop)
        certified = sorted(L.read_manifest(propdir).get("certified", {}), key=L.natural_key)
        if not certified:
            print(f"[smt_probe] {os.path.relpath(propdir, L.BOOK_ROOT)}: no certified nodes in manifest "
                  f"— run `check_step.py {prop} --all` first. Skipping.")
            continue
        cache = {} if reprobe else read_cache(propdir, caps)
        try:
            for node in certified:
                ch = _cone_hash(propdir, node)
                hit = cache.get(node)
                if hit and hit.get("cone_hash") == ch and not reprobe:
                    res = hit["result"]                  # reuse — no build
                else:
                    if max_budget and spent > max_budget:
                        print(f"[smt_probe] budget {max_budget}s exhausted — stopping (spent {spent:.0f}s).")
                        break
                    res = probe_node(propdir, node, caps=caps, wall_pad=wall_pad, trace=True,
                                     probe_substeps=probe_substeps)
                    spent += sum(m["elapsed_s"] for m in res["monolithic"])
                    spent += sum(s["elapsed_s"] for s in res["substeps"])
                    cache[node] = {"cone_hash": ch, "result": res}
                if not _is_failure(res):
                    print(f"[smt_probe] {res['id']}: closes monolithically — NOT a failure, skipping.")
                    continue
                if res["failure_mode"] == "REVIEW":      # timed out but tag is unsound → never silent
                    print(f"[smt_probe] ⚠ {res['id']}: TIMED OUT but flagged REVIEW (body introduces a "
                          f"witness the probe can't preserve) — NOT cataloged. Human must inspect: "
                          f"{res['evidence'][0] if res['evidence'] else ''}")
                    continue
                res["lean_toolchain"] = _toolchain()
                res["systemE_commit"] = _git_rev()
                rel = write_entry(out_dir, res, res.get("query", ""))
                if rel:
                    entries.append(res)
                    print(f"[smt_probe] cataloged {res['id']} ({res['failure_mode']}) → {rel}")
        finally:
            write_cache(propdir, caps, cache)
    catalog = {
        "generated": "",   # stamp externally if needed (no wall-clock in this lib's contract)
        "solver": "z3+cvc5 portfolio (systemE.solverTime)",
        "theory_source": "SystemE/Meta/Smt/EuclidTheory.lean",
        "lean_toolchain": _toolchain(),
        "systemE_commit": _git_rev(),
        "entries": [{k: v for k, v in e.items() if k != "evidence"} | {"evidence": e["evidence"]}
                    for e in entries],
    }
    with open(os.path.join(out_dir, "catalog.json"), "w", encoding="utf-8") as f:
        json.dump(catalog, f, indent=2)
    with open(os.path.join(out_dir, "README.md"), "w", encoding="utf-8") as f:
        f.write(CATALOG_README)
    print(f"\n[smt_probe] catalog: {len(entries)} entr(y/ies) under {os.path.relpath(out_dir, L.BOOK_ROOT)} "
          f"({sum(e['failure_mode']=='A' for e in entries)} A, {sum(e['failure_mode']=='B' for e in entries)} B).")
    return 0


# ── CLI ─────────────────────────────────────────────────────────────────────────────────────────────
def _parse_opts(args):
    opts = {"caps": [30], "wall_pad": 30, "trace": True, "probe_substeps": False,
            "max_budget": None, "json": False, "reprobe": False, "jsonl": None}
    rest = []
    i = 0
    while i < len(args):
        a = args[i]
        if a == "--caps":
            opts["caps"] = [int(x) for x in args[i + 1].split(",")]; i += 2
        elif a == "--wall-pad":
            opts["wall_pad"] = int(args[i + 1]); i += 2
        elif a == "--no-trace":
            opts["trace"] = False; i += 1
        elif a == "--probe-substeps":
            opts["probe_substeps"] = True; i += 1
        elif a == "--max-budget":
            opts["max_budget"] = float(args[i + 1]); i += 2
        elif a == "--json":
            opts["json"] = True; i += 1
        elif a == "--jsonl":
            opts["jsonl"] = args[i + 1]; i += 2
        elif a == "--reprobe":
            opts["reprobe"] = True; i += 1
        else:
            rest.append(a); i += 1
    return opts, rest


def mode_clean():
    n = 0
    for p in glob.glob(os.path.join(L.BOOK_ROOT, "**", "_probe_*.lean"), recursive=True):
        try:
            os.unlink(p); L._invalidate_target(L.target_of(p)); n += 1
            print(f"  removed {os.path.relpath(p, L.BOOK_ROOT)}")
        except OSError:
            pass
    print(f"[smt_probe --clean] removed {n} stray probe file(s).")
    return 0


def main(argv):
    if not argv:
        print(__doc__)
        return 2
    try:
        if argv[0] == "--clean":
            return mode_clean()
        if argv[0] == "--emit-catalog":
            if len(argv) < 3:
                print("FAIL: --emit-catalog needs <out_dir> and at least one <propdir>.")
                return 2
            opts, rest = _parse_opts(argv[2:])
            return emit_catalog(argv[1], rest, caps=opts["caps"], wall_pad=opts["wall_pad"],
                                probe_substeps=opts["probe_substeps"], max_budget=opts["max_budget"],
                                reprobe=opts["reprobe"])

        propdir = L.propdir_of(argv[0])
        opts, rest = _parse_opts(argv[1:])

        def as_node(tok):
            return f"step{tok}" if tok.isdigit() else tok

        if rest and rest[0] == "--classify-only":
            if len(rest) < 2:
                print("FAIL: --classify-only needs a <node>.")
                return 2
            node = as_node(rest[1])
            cat, evidence = classify_node(propdir, node)
            print(f"[smt_probe --classify-only] {node}: {cat}")
            for e in evidence:
                print("  - " + e)
            if cat == "B":
                print("  instantiated in-theory axioms: " + (", ".join(instantiated_axioms(propdir, node)) or "(none)"))
            return 0

        if rest == ["--all-nodes"]:
            nodes = [n for n, _ in L.audit_order(propdir)]
        elif len(rest) == 1 and not rest[0].startswith("-"):
            nodes = [as_node(rest[0])]
        else:
            print(__doc__)
            return 2

        cache = {} if opts["reprobe"] else read_cache(propdir, opts["caps"])
        results, spent, n_cached, n_run = [], 0.0, 0, 0
        # --jsonl streams one record per node AS IT COMPLETES (append, flushed) → a scancel mid-run still
        # leaves a valid partial file, and it's tail-able. Truncate once at start.
        jsonl_fh = open(opts["jsonl"], "w", encoding="utf-8") if opts["jsonl"] else None
        try:
            for node in nodes:
                ch = _cone_hash(propdir, node)
                hit = cache.get(node)
                if hit and hit.get("cone_hash") == ch and not opts["reprobe"]:
                    res = hit["result"]                  # unchanged since last probe — reuse, no build
                    n_cached += 1
                    if not opts["json"]:
                        _print_result(res, cached=True)
                    results.append(res)
                    if jsonl_fh:
                        jsonl_fh.write(json.dumps(flat_record(res)) + "\n"); jsonl_fh.flush()
                    continue
                if opts["max_budget"] and spent > opts["max_budget"]:
                    print(f"[smt_probe] budget {opts['max_budget']}s exhausted — stopping (the rest stay "
                          f"un-probed; re-run to continue, already-probed nodes are cached).")
                    break
                res = probe_node(propdir, node, caps=opts["caps"], wall_pad=opts["wall_pad"],
                                 trace=opts["trace"], probe_substeps=opts["probe_substeps"])
                spent += sum(m["elapsed_s"] for m in res["monolithic"])
                spent += sum(s["elapsed_s"] for s in res["substeps"])
                cache[node] = {"cone_hash": ch, "result": res}
                n_run += 1
                results.append(res)
                if not opts["json"]:
                    _print_result(res)
                if jsonl_fh:
                    jsonl_fh.write(json.dumps(flat_record(res)) + "\n"); jsonl_fh.flush()
        finally:
            write_cache(propdir, opts["caps"], cache)    # persist even if interrupted/budget-stopped
            if jsonl_fh:
                jsonl_fh.close()
        if opts["json"]:
            print(json.dumps(results if len(results) > 1 else (results[0] if results else None), indent=2))
        elif len(nodes) > 1:
            print(f"\n[smt_probe] {n_run} node(s) probed, {n_cached} reused from cache." +
                  (f" → {opts['jsonl']}" if opts["jsonl"] else ""))
        return 0
    except L.FaithfulError as e:
        print(f"ABORT (structural/naming error — refusing to proceed): {e}")
        return 2


def _print_result(res, cached=False):
    print(f"\n[smt_probe] {res['id']}  ({res['failure_mode']})" + ("  [cached]" if cached else ""))
    if res["failure_mode"] in ("C", "REVIEW"):
        print(f"  classified {res['failure_mode']} — not a solver-failure case; not probed.")
        for e in res["evidence"]:
            print("    - " + e)
        return
    print(f"  goal: {res['goal']}")
    for m in res["monolithic"]:
        print(f"  monolith @ {m['cap_s']}s cap: {m['status']}  ({m['elapsed_s']}s)")
    if res["failure_mode"] == "B" and res["instantiated_axiom"]:
        print(f"  instantiated in-theory axiom(s): {', '.join(res['instantiated_axiom'])}")
    if res["substeps"]:
        fast = sum(1 for s in res["substeps"] if s["status"] == "pass")
        print(f"  substeps: {fast}/{len(res['substeps'])} close fast "
              f"(max {max((s['elapsed_s'] for s in res['substeps']), default=0)}s)")
    print(f"  {'IS' if _is_failure(res) else 'NOT'} a catalog candidate "
          f"(certified={res['certified']}, query_captured={bool(res['query'])}).")


if __name__ == "__main__":
    try:
        sys.stdout.reconfigure(line_buffering=True)
        sys.stderr.reconfigure(line_buffering=True)
    except Exception:
        pass
    sys.exit(main(sys.argv[1:]))
