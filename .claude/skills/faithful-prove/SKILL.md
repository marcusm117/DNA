---
name: faithful-prove
description: >
  PHASE B of making a Euclid proof faithful (LeanEuclidPlus, Book 2): prove each Euclid sentence's
  step, IN ISOLATION, using the recursive SF/SP/P atom and the `check_step.py` script. Main's sentence
  bodies stay `:= by sorry` the whole time; the SCRIPT does all wiring/trace_state transiently — you
  only ever write proof bodies and add `have`+backing-file decompositions. Use AFTER the sentence map
  is written and human-approved (`faithful-map` / Phase A). When `check_step.py <propdir> --all` exits
  0, STOP — Phase C (the human running `wire_main.py`) is mechanical, not a skill. Delegates the actual
  proving to `prove-euclid`. Invoked with a path, e.g. `/faithful-prove Book2/Prop04/Main.lean`.
---

# Phase B — prove each step with the recursive SF/SP/P atom (the scripts own all wiring)

By now (via `faithful-map` / Phase A, human-approved) `Book<N>/PropNN/Main.lean` is the proposition
signature + `euclid_intros` + the object-producing constructions + one
`euclid_sentence "loc" "txt" (stepN : <claim>) := by sorry` per Euclid sentence + the intro/conclude
bookends + the trailing `exact`/`rw` chain. **Every logical body is `:= by sorry`. There are no step
files yet.** Your job: create and prove each step's backing file, recursively decomposing until every
build is ≤30s — WITHOUT ever wiring Main or building an all-wired container yourself. A script does
all of that.

> **READ `prove-euclid` FIRST — hard prerequisite.** All actual proving (decompose → sorry-skeleton →
> fill, the pattern gallery, the 30s rule, explicit `euclid_apply` chains) is `prove-euclid`'s job.
> This skill is the faithfulness wrapper: it tells you the FILE STRUCTURE and the SCRIPT-DRIVEN
> verification loop around that proving.

---

## THE MENTAL MODEL — ONE recursive atom, four nouns (internalize this; nothing else)

- **Container** = any `.lean` file with a tactic proof: `Main.lean`, any `stepN.lean`, a sub-file, …
  recursively. A container may mix REAL `euclid_apply` proof work (must build ≤30s) AND
  `have … := by sorry` sub-nodes.
  > **CONVENTION — `Main` is NOT a node** (it's the root container; it has no backing file, no claim,
  > no parent). So you NEVER pass `Main` as a node argument. The ONLY no-node command is
  > `check_step <propdir> --provable` = "build Main, tolerate sorry" (the Phase-A skeleton check; Main
  > having no parent gets only the build, not SF/SP). `--sufficient`/`--suppliable` with no node, or
  > with `Main`, FAIL with a message saying exactly this. To check a SENTENCE inside Main, pass that
  > sentence's node (`step5`), whose container is Main.
- **Goal node** = a named `:= by sorry` body. Two forms, identical at the proof level:
  - **Main only:** `euclid_sentence "loc" "txt" (stepN : C) := by sorry`  (from Phase A — don't add these).
  - **anywhere:** `have <name> : C := by sorry`  (you add these when decomposing).
- **Backing file** = the helper that proves a node. **NAMING LAW (the script enforces it, abort-loud):**
  > node name  ≡  `<name>.lean` basename  ≡  `theorem helper_<book>_<prop>_<name>`.
  > `have step27_bigsq : … := by sorry` ↔ `step27_bigsq.lean` ↔ `theorem helper_2_4_step27_bigsq` (book 2,
  > prop 4). The `<prop>` segment is what keeps `helper_2_2_step1` (Prop02) and `helper_2_3_step1`
  > (Prop03) DISTINCT constants — so the whole book builds without an `environment already contains
  > 'helper_…'` collision. (The node/file basenames stay the short `step27_bigsq`; only the theorem name
  > carries the book+prop prefix.)
  Each name maps to exactly ONE backing FILE; a `have` of that name may OCCUR in several parents (a
  reused helper — see "Shared logic" below). An `euclid_sentence` step name is unique (one per sentence).
- **Wiring** = a node's `sorry` replaced by
  `euclid_apply (helper_<book>_<prop>_<name> <objs> (by assumption)…); (try split_ands) <;> assumption` **PLUS
  the `import Book<N>.PropNN.<name>` that makes that helper resolve** — wiring is BOTH halves. The helper
  is **FULLY APPLIED**: its objects positionally, then **one `(by assumption)` per hypothesis binder**.
  Full application means the `euclid_apply` term has no remaining antecedent arrow, so **the wire does
  ZERO SMT** — every hypothesis is discharged by core-Lean `assumption` (a <1s type-match over the local
  context, *including unnamed/inaccessible `a✝` hyps*), and the goal is closed STRUCTURALLY by
  `(try split_ands) <;> assumption` (the helper's conclusion is `obtain`'d and destructed into atoms by
  `euclid_apply`, so each conjunct matches an atom — no solver). The closer is **NOT `euclid_finish`**:
  `euclid_finish` would fall through to the SMT solver over the parent's full context and blow the 30s
  wall even for a trivial leaf (a bare `euclid_finish` is tolerated only as a *legacy* shape the scripts
  recognize, never the form they emit). The only SMT left is inside helper **bodies** and a container's
  **trailing tactics** (each bounded + P/SF-checked). This is the no-timeout guarantee: the wire is
  free; all cost lives in checked ≤30s places.
  **ONLY the scripts ever write wiring (body + helper import) or `trace_state`. You NEVER type any of
  them into a file.** You write proof bodies and add `have`+backing-files; the script wires + imports
  transiently and always reverts.

  > **THE SIGNATURE LAW (this is what the assumption-wire enforces):** a helper's hypothesis binders must
  > be EXACTLY facts present at the call site, in the LITERAL form the parent has them. If `(by
  > assumption)` can't find a hyp, SP fails loudly — that's the signal the signature is wrong. The fix is
  > NEVER to make Main derive it: **drop that hyp from the signature and DERIVE it inside the helper body**
  > (an `euclid_assert`/`euclid_apply` in the body — bounded ≤30s leaf SMT). Two corollaries:
  > (1) a fact NOT in `--context` is not a hypothesis — derive it in-body; (2) a fact in a DIFFERENT
  > form/orientation than context (distance/angle symmetry, a packaged abbrev like `formTriangle`/
  > `formParallelogram` vs its atomic conjuncts) fails `assumption` (it's exact up to defeq only) — take
  > the ATOMS the parent literally has, or derive the reoriented fact in-body. Hyps are matched by TYPE,
  > so differently-NAMED-but-same-type facts wire automatically — `@args` is OBJECT-ONLY, never for hyps.

### THE IMPORT INVARIANT (the LLM never imports a helper/step file)
A dev-state container imports ONLY `SystemE` + the **cited-proposition** imports its own proof uses
(e.g. `import Book.Prop29` for an `euclid_apply (proposition_29'''' …)` you wrote) **+ any
`Helpers.*` shared-lemma file it applies** (see below) — those are proof content you DO write. It
imports NONE of its pipeline backing/step files; the script adds an `import Book<N>.PropNN.<name>` only
while it transiently wires that node, and removes it on revert. This is what makes per-node checks fast
and isolated (checking node N pulls in only N's backing olean, not every sibling).
`check_step … --check` flags any stray `Book<N>.PropNN.*` (the prop's OWN-prefix pipeline) import as an
error — it does NOT flag `Helpers.*` (a different prefix), so a library import is permanent and
legal. **Reach a PIPELINE sub-lemma ONLY as a `have`-node** (`have <sub> : <concl> := by sorry`; the
script wires + imports it) — NEVER hand-write a pipeline `euclid_apply` or a pipeline import.

> **THE LIBRARY EXCEPTION — `Helpers/` lemmas are applied INLINE, by you, with a PERMANENT import.**
> `LeanEuclidPlus/Helpers/{OffLine,SameSide,Area,RightAngle,Parallel}.lean` holds pre-proved generic
> lemmas for the recurring off-line / sameSide / area-recast / right-angle / parallel-transitivity facts
> (see `euclid-figures`). Unlike a pipeline backing file, a library lemma is NOT a `have`-node and NOT
> script-wired: you write `import Helpers.OffLine` (it stays — different prefix, never flagged) and
> discharge the fact in-place as `have F : <claim> := <lemma> obj… (by assumption)…` (or
> `by euclid_apply (lemma …)`). This is pipeline-legal: a pre-proved lemma application does ZERO SMT
> search (just instantiation), so it costs nothing against the 30s wall, and the resulting `F : <claim>`
> sits in context for downstream wires to discharge by `assumption` exactly as a backing-file node would.
> **So these facts take NO backing file** — that is precisely how a step that used to be ~10 leaf files
> collapses to ~1–3. If the lemma you need doesn't exist yet for your atom-shape, PROMOTE a sibling into
> the Helpers file (then the human rebuilds that Helpers target) rather than spawning a one-off backing leaf.
>
> **GRANULAR IMPORTS — import the SPECIFIC sub-module, NEVER the `Helpers` aggregator.** Write
> `import Helpers.OffLine` (or `.SameSide`, `.Parallel`, …) — only the ones you actually use. Do NOT
> `import Helpers` (the aggregator): it pulls in EVERY helper, so adding any new lemma anywhere would
> invalidate your file and force a needless rebuild. The `Helpers` aggregator exists ONLY as the
> `lake build Helpers` target root (build-all-helpers), never as a proof-file import.
>
> **SUPPLIABILITY — the lemma's hyps must still be Main-suppliable atoms.** A library lemma's hypotheses
> are discharged by `(by assumption)` at the inline site, so each must be a fact the container already
> has VERBATIM — same as any wired node. Watch the distinctness hyps in particular: the no-witness forms
> (`offLine_of_parallel_simple(')`, `sameSide_of_parallel_both`) take an explicit `L ≠ M` (it's essential
> — without it the claim is false), so the container must carry that `L ≠ M`. If it doesn't, derive it
> first (a one-term `fun h => hoff (h ▸ hon)` from an off-line anchor) or pick the witness-bearing sibling
> that establishes distinctness itself.

### THE PRIME DIRECTIVE (the one invariant you must never break)
> **At every stage, every `.lean` file in the prop folder builds with its current sorries. If any file
> ever fails to build, STOP and fix that before doing anything else.**

---

## THE RECIPE — `PROVE(container)` — apply it to each Main sentence, recursing as needed

Go through Main's sentences **IN ORDER — step1, then step2, …, then the last** — ONE at a time, fully
finishing each before the next. NOT any order, NOT in parallel. Reason: a later step's hypotheses are
typically EARLIER steps' claims (e.g. a summing step takes the prior area steps as hyps), so by the
time you reach stepN every fact it can rely on is already settled and correctly shaped — proving out of
order makes a step's suppliable context unstable. Within each step, recurse the same way over every
backing file you create. (Run `--all` ONLY at the very end — see THE LOOP — never to drive this.)

> **⛔ START WITH step1 ONLY — do NOT pre-stub the other steps.** Your literal first action is: create
> `step1.lean`, prove its WHOLE cone, and `check_step --subtree step1`-confirm it GREEN — *before you
> create `step2.lean` or write/stub ANY other step's backing file*. The Main sentence bodies are
> already `:= by sorry` from Phase A (leave them); what you must NOT do is lay down step2…stepN's
> backing files up front "to see the shape." Finish step1's file and cone, then and only then create
> step2's. ("Fully finishing each before the next" means the step's backing FILE + its sub-cone, not
> just the recursion inside it.) At any moment the ONLY new backing file(s) on disk are for the single
> step you are currently on.

```
Is this goal an off-line / sameSide / area-recast / right-angle-co-interior / parallel-transitivity fact?
  YES → does a Helpers/ lemma match the ATOMS my context has (see euclid-figures Families 1/3/6/7)?
        YES → discharge it INLINE: `import Helpers.<File>` (permanent) + `have F : <claim> :=
              <lemma> obj… (by assumption)…`. NO backing file, NO have-node. This is the file-count win.
        NO (close, but my atom-orientation/witness isn't covered) → PROMOTE a sibling lemma into that
              Helpers file (match your literal atom), have the human rebuild it, then apply inline as above.
  NO (genuine content — betweenness / assembly / proposition-citation) → continue:

Can I close this goal directly (real euclid_apply chain, no new node) and build it ≤30s?
  YES → write that proof; verify it green with `check_step Book<N>/PropNN --provable <thisnode>` → DONE.
  NO  → introduce a sub-fact F. NEVER guess its signature:

  (a) SEE THE CONTEXT (script-owned trace_state; addressed BY NODE NAME):
        python3 scripts/check_step.py Book<N>/PropNN --context <node>
      Prints the REAL hypotheses available at that node. For a brand-new fact F, first stub
      `have F : <claim> := by sorry` and use it to close the goal, then --context F.
      ⚠ NOW AUTHORITATIVE FOR THE SIGNATURE: since the wire discharges hyps by `(by assumption)` (no
      SMT), F's hypothesis binders must be facts that ACTUALLY appear in this --context dump, in the
      LITERAL form shown (an unnamed `a✝` hyp still counts — assumption matches by type). A fact NOT in
      the dump is not a hypothesis → derive it in F's body. (The dump shows packaged abbrevs already
      UNFOLDED to atoms — so take the atoms, never the package.)

  (b) RUN SF — Sufficient (cheapest, FIRST, before any backing file exists):
      with `have F : <claim> := by sorry` in place and USED to close the parent,
        python3 scripts/check_step.py Book<N>/PropNN --sufficient F
      builds the CONTAINER (claim as sorry, no wiring). Green ⟹ the claim is well-typed AND F suffices
      to close the goal. Fails ⟹ F is bogus → fix the CLAIM; do not start proving it.
      (Caveat: for a MAIN SENTENCE node — vs a `have` — SF only confirms well-typedness, because Main's
      sentences are independent `have`s that don't consume each other; SP is the discriminating check
      there. For a `have`/container, SF genuinely tests sufficiency + that the trailing tactics close.)

  (c) CREATE the backing file F.lean (naming law):
        import SystemE   (+ the specific Book.PropMM / Book2.PropMM.Main it CITES — proposition
                          citations only; NEVER import another helper/step file)
        set_option systemE.solverTime 30 in
        theorem helper_<book>_F <objects from (a)> <hyps from (a)> : <claim> := by sorry
      Hyps must be EXACTLY facts present in F's --context dump, in their LITERAL form (they'll be
      discharged by `(by assumption)` at the wire — a type-match, no SMT). If a proof needs something
      NOT in context, that something becomes ANOTHER `have`+backing-file (recurse) OR is derived in F's
      body (e.g. `euclid_assert <fact>` before you use it) — NEVER an un-suppliable hypothesis, and
      NEVER something Main has to derive for F.

  (d) RUN SP — Suppliable (BEFORE proving; order matters):
        python3 scripts/check_step.py Book<N>/PropNN --suppliable F
      The script wires ONLY F in its container (objects + one `(by assumption)` per hyp), builds,
      reverts. This is a fast, SMT-free type-match check. PASS ⟹ every F hypothesis is present at the
      call site. FAIL ⟹ a `(by assumption)` couldn't find a hyp (`tactic 'assumption' failed`) → that
      hyp is absent or in a different form → **remove it from F's signature and derive it in F's body**
      (or fix its form to match context). Re-run.
      ⚠ SHARED helper, ONE site failing: `--suppliable F` runs SP at EVERY call site of F. If it PASSES
      at 7 sites and FAILS at ONE, the problem is LOCAL to that site — that hyp isn't present THERE. Read
      the FAIL's `@ <file>` tag, fix THAT site (slim F's signature so it only takes what's present
      everywhere, deriving the rest in-body; or split F). Do NOT keep re-running the full multi-site
      sweep or edit a DIFFERENT node hoping it helps — the fix is at the failing site; the 7 passing ones
      are already settled.

  (e) RUN P — Provable: PROVE(F.lean) — RECURSE, same recipe one level down, until F builds ≤30s.
      `check_step.py Book<N>/PropNN --provable F` builds F.lean and reports zero-sorry (done) or the
      file:lines where sorries remain. P is LEAF-ONLY: if F.lean is itself a CONTAINER (you gave it its
      own `have` sub-nodes), P reports "container, not built" — that's a PASS; its trailing tactics (the
      `linarith [...]` after its `have`s) are checked by building F.lean with sorries tolerated (the
      SF-side container build), and its leaves by their own P. Don't try to build a container to prove it.
```
> **In practice, just run `python3 scripts/check_step.py Book<N>/PropNN <node>` (no flag).** It runs
> SF → SP → P in that order and stops at the first failure — telling you exactly what to fix next. The
> individual `--sufficient`/`--suppliable`/`--provable` flags are occasional diagnostics; the bare
> command is the everyday driver.
> **ALL builds go through `check_step` — the agent is HARD-DENIED raw `lake build` / `safe_build.sh`.**

- **30s is recursive and absolute.** Every file carries `set_option systemE.solverTime 30 in`; every
  `check_step` build is also killed at 30s wall. Exceed EITHER ⟹ the node is too big → **decompose
  into more backing files; NEVER raise a cap.** "Simplify until 30s works" is the whole loop.
- **A >30s timeout is ALWAYS a P or container-build cost — never an SP cost (SP does no SMT).** Since
  the wire discharges hyps by `(by assumption)` (a <1s type-match), SP cannot time out: an SP FAIL means
  a hypothesis isn't present (signature wrong — slim it / derive in-body), full stop. Timeouts live in
  exactly two SMT places, both diagnosable:
  - **(i) A LEAF body is too big** — its `euclid_apply` chain + `euclid_finish`/`euclid_assert`s do too
    much. Seen as P >30s. Remedy: pull work into more `have`+backing-file sub-nodes (the usual decompose).
    > **⛔ A SINGLE oversized `euclid_apply (axiom …)` is STILL decomposed — NOT re-permuted.** The most
    > common >30s leaf is one axiom whose PRECONDITION is fat: e.g. `rectangle_area` needs
    > `formParallelogram a b c d …`, which unfolds to ~10 conjuncts (incidences + `distinctPointsOnLine`
    > + a `sameSide` + two non-intersections), and `euclid_finish` blows the wall SEARCHING for them at
    > the call. The fix is to DECOMPOSE the precondition, not to guess a cheaper call: **establish the
    > precondition (or just its hard conjunct) as its OWN `have`+backing sub-node, then `euclid_apply`
    > the axiom with that fact in hand** (prove-euclid rule #8 — replace SMT search with explicit
    > application; e.g. derive the lone `a.sameSide f CD` via `intersection_lines_opposing` in its own
    > leaf, then the `formParallelogram` closes from atoms, then `rectangle_area` fires with nothing to
    > search). **Re-running the SAME axiom with a different argument/vertex/line ORDER — hoping one
    > orientation is cheaper — is the forbidden restate-and-hope: it is NOT decomposing.** If you've
    > rewritten a leaf twice without adding a sub-node, STOP permuting and extract the precondition.
    > **⚖️ TIMEOUT TRIAGE — two opposite causes, opposite fixes; diagnose which before acting.** A >30s
    > leaf is one of:
    >  - **a genuinely-needed NON-TRIVIAL fact is missing** (e.g. `a.sameSide f CD` for an interior
    >    vertical) → ADD a sub-node that derives it. ✅
    >  - **a TRIVIAL fact `euclid_finish` should find instantly is drowning in a BLOATED context** (too
    >    many hypotheses → the solver searches them all) → the fix is to **SLIM the signature to the
    >    handful of hyps actually needed, NOT add a node.** Adding a leaf for a trivial fact like
    >    `¬a.onLine CD` is OVER-decomposition — and it won't even help, because the new leaf INHERITS the
    >    same bloated signature and times out too. (This was the step6 rabbit-hole: a `step6_aoff`/`_foff`
    >    tower for trivial off-line facts, each still timing out, until the signatures were slimmed.)
    >  Rule of thumb: if a sub-node for an *obvious* fact times out, you have a context-size problem, not a
    >  hardness problem — cut hypotheses, don't add depth.
    > **♻️ REUSE a sibling's fact — don't re-derive a precondition from scratch.** Before hand-building an
    > axiom's precondition, check whether an EARLIER step (or a sister prop) already establishes it, and
    > take it as a HYPOTHESIS / shared sub-node. step6 reuses `step5_edf` (the `between e d f` step5
    > already proved) and gets `formParallelogram`'s hard `sameSide` conjunct from the CONTAINING square's
    > parallelogram (`step6_hsq`) — instead of re-deriving the whole figure from incidences. Re-proving a
    > `formParallelogram`/`between`/`sameSide` that a sibling already produced is wasted depth; the analog
    > step (e.g. Prop02 step4, your own step5) shows the TECHNIQUE (hand the figure-fact in as a hyp), not
    > just an orientation to copy.
  - **(i-b) A LEAF closes with one ALL-IN-ONE `euclid_finish`** — after `euclid_apply (axiom …)`, a
    single `euclid_finish` that must discharge the axiom's precondition AND match its conclusion AND do
    the length/area algebra is doing three jobs at once → timeout. Remedy: **split the algebra out** —
    pull each length/area rewrite into its own `have h… := by euclid_finish` then `rw [h…]`/`linarith`,
    so the FINAL closer only has to match the goal shape (the lean-closer pattern: step5/step6 end on a
    thin `rw [...]; ring`/`euclid_finish`, NOT a fat one). Fewer obligations per solver call = under 30s.
  - **(ii) A CONTAINER's trailing tactics are too big** — the proof work AFTER its `have`s (the
    `euclid_finish`/`linarith` that assembles sub-node claims into the container's goal). These run when
    the container is built with its sub-nodes as sorry (the SF-side build that SF and `--all`/`--subtree`
    do for a container) — NOT during a sub-node's SP (SP stubs the trailing tactics to `sorry` so they
    never run). Remedy: if that tail is heavy SMT, factor it (e.g. `linarith` over locked area-equalities
    instead of one big `euclid_finish` over area atoms — see step27_decomp), or push a sub-group into its
    own intermediate `have`+backing file.
  - There is NO "fat wire" cause anymore — that was the OLD SMT-discharge wire. A fat signature no longer
    costs time at the wire (assumption is cheap); it only matters for SP *correctness* (every hyp must be
    present). Still prefer minimal signatures (minimal-hyp law) — but for clarity/suppliability, not speed.
- **Keep containers reasonable, but the OLD crowding tax is gone.** SP/SF still elaborate sibling claim
  TYPES (cheap typechecking), but no longer RE-DISCHARGE a fat wire by SMT — so piling siblings no longer
  tips a node over 30s at the wire. Crowding now only matters if a container's TRAILING TACTICS genuinely
  need all siblings at once and that tail is heavy SMT; if so, NEST (push a sub-group into its own
  intermediate `have`+backing file) so the tail is smaller.
- **Shared logic → ONE generic backing file, reused as a `have <name>` node in several parents —
  BUT ONLY WHILE its full signature is suppliable at EVERY site** (i.e. every hyp it declares is present,
  by type, at each call site — the assumption-wire's requirement). If the same fact recurs, write a
  `have <name> : <claim> := by sorry` in each parent, backed by ONE `<name>.lean` (theorem
  `helper_<book>_<prop>_<name>`, quantified over its own binders). The scripts handle it: SF/SP run at EVERY
  call site, P runs ONCE on the single backing file, `--all` shows "SP [N call sites] + P".
  > **The no-duplicate rule is NARROW: it forbids copy-pasting an IDENTICAL proof BODY into two files
  > (two `<name>.lean` for one name is a hard error). It does NOT force one fat lemma to stay monolithic
  > when sharing HURTS.** A shared helper is only correct while its whole signature is suppliable at
  > every site. The moment one site can't supply a hyp — its SP fails there because that hyp is absent or
  > differently-formed at THAT site — **SPLIT it**: give that site a slimmer helper carrying only the
  > hyps present there (deriving the rest in-body), even if the new helper's body OVERLAPS the original's.
  > Divergent-signature helpers that happen to share some `euclid_apply`s are NOT "duplicated proofs" —
  > they're correctly-scoped lemmas; the rule against duplication is about not maintaining the same proof
  > twice, not about forcing a one-size signature that isn't suppliable everywhere.
  Two flavors of a genuinely-shared (affordable-everywhere) helper, by whether the call args match across sites:
  - **Same objects at each site** (the parents share names — e.g. both work with Main's `a b c`): just
    write the identical `have <name> : <claim> := by sorry`. Wiring defaults to the helper's binder
    names; it resolves because those names are in scope at each site.
  - **Different objects per site** (e.g. the same lemma on figure `h g f d` in one step and `c b k g`
    in another): the helper is generic; each call site gives ITS actuals via a `-- @args:` line on the
    line DIRECTLY ABOVE that node:
    ```
        -- @args: h g f d
        have rectarea : <claim about h g f d> := by sorry
    ```
    The script wires `euclid_apply (helper_<book>_rectarea h g f d (by assumption)…); (try split_ands)
    <;> assumption` at that site (and `c b k g …` at the other). The `@args` tokens are the helper's
    OBJECT binders ONLY,
    in order, count must match (else `--check` errors); they must be names in THAT parent's scope (else
    SP fails — the `unknown identifier` hint reminds you). Hypotheses are NEVER in `@args` — they're
    discharged by `(by assumption)` (type-match), so a differently-named-but-same-type hyp needs no
    annotation. You still NEVER write the `euclid_apply` yourself — only the `-- @args:` data line; the
    script authors the call. (The annotation is the ONLY hand-written comment the pipeline reads; it
    survives wiring untouched.)
- **You never wire Main and never build an all-wired container.** Don't use `--all` as your driving
  loop or to find failures (it re-checks EVERY node — minutes wasted); drive with per-node
  `check_step <node>` and confirm a container/step with `check_step --subtree <node>` (scoped to that
  cone). To pick up a proof whose state you don't know, see RESUMING below (the one case `--all` is a
  starting snapshot). Otherwise `--all` is the END only — exactly ONCE.
- **LAUNCH `--all` (and any long `--subtree` over a deep shared cone) WITH `run_in_background: true`.**
  The final `--all` re-walks every node across all call-sites and can run 2.5–7 HOURS wall-clock — a
  foreground call would block the whole turn on one tool use. Backgrounded, the harness pings you when it
  exits, and you stay free meanwhile. This changes only *how* you launch the final audit — NOT the "run
  `--all` ONCE, at the very end, never to hunt a failure" rule above.
  - **Watching progress: READ the job's output FILE (`…/tasks/<id>.output`) with the Read tool.** When
    the harness backgrounds a build it prints that path and says "Read on that file path"; `check_step`
    line-buffers its stdout, so `--all`/`--subtree`'s per-node `✓ <node>` lines (and the deepest `✗ …` on
    failure) appear in that file AS THEY HAPPEN. That is the proven live channel — just Read it again
    whenever you want a progress snapshot. (Do NOT use `TaskOutput`/`block=true` to "peek": block=true
    WAITS for the whole job — correct only when you actually want to wait for completion — and the
    non-blocking form may show nothing because that capture layer doesn't always stream. The output FILE
    does.) There is NO separate per-node log file the script writes — do NOT look for
    `.lake/.../<node>.log.json` (those are Lake build artifacts, not progress logs). And NEVER poll with
    `sleep N; tail …` / `ps`/`grep` on the process: those are foreground spin-waits that block the turn
    AND are blocked by the bash-hygiene hook. If the job's
    output isn't pollable in your harness, just wait for the completion ping — do not invent a workaround.

---

## THE DIAGRAM — intuition aid for choosing the proof path (NOT a source of truth)
Look at `Book<N>/data/diagrams/<N>.png` to SEE which points are collinear, which side of a line a
point is on, betweenness, and figure vertex order — exactly the `between`/`sameSide`/`formParallelogram`
relations that decide WHICH axiom/prop to reach for and which hypotheses to derive. This is intuition
for *how to prove*, and it is SAFE here in a way it is NOT in Phase A: the claims are frozen (gate A),
your judgement is never trusted, and the BUILD is the judge — if a diagram-suggested fact isn't
actually entailed, SP/P simply fails, so a wrong hunch is caught mechanically, never committed. RULES:
you may use the diagram to decide the proof path; you may NEVER use it to change a claim (claims are
guarded by `check_steps.py`), and every fact is still PROVEN via `euclid_apply`/`euclid_finish` — never
asserted "because the picture shows it." Use `--context` for what's *available*; the diagram for what's
*true to aim at*.

## SYSTEM-E QUICK REFERENCE (the area-heavy surface you actually prove with)
> **For the recurring figure-reasoning goal-shapes** (sameSide / off-line / line-distinctness /
> pasch-betweenness / `formParallelogram`-`formTriangle` assembly / `rectangle_area`-`sum_parallelograms_area`
> / parallel-angle props), see the **`euclid-figures`** skill — it lists goal-shape → axiom-chain → gotcha
> recipes grounded in proven files (the done Prop01/02/03 + Prop04's certified leaves). It's the concrete companion to the timeout-triage
> bullets above; consult it when a sub-node matches one of those shapes.

Grep `SystemE/Theory/Inferences/{Metric,Transfer,Diagrammatic}.lean` + `Relations.lean` for exact
signatures; the high-value ones:
- **Convention:** "rectangle contained by X,Y" = `|X|*|Y|`; "square on X" = `|X|*|X|`; no square axiom
  (it's the right-angled case of `rectangle_area`). Figure areas = sums of `Triangle.area △ p:q:r`;
  `Triangle.area` is permutation-invariant (`area_symm_1/2`, Metric.lean) — order is cosmetic.
- `rectangle_area a b c d AB CD AC BD : formParallelogram … ∧ ∠a:c:d = ∟ →`
  `(area△a:c:d + area△a:b:d = |a─b|*|a─c|) ∧ (area△b:a:c + area△b:d:c = |a─b|*|a─c|)`.
- `parallelogram_area …` (diagonal triangle-area identity); `sum_parallelograms_area a b c d e f … :`
  `formParallelogram … ∧ between a e b ∧ between c f d →` 4 sub-triangles sum to 2 halves (split/glue
  rectangles). `sum_areas_*`, `degenerated_area_*` (Transfer); `area_gte_zero` (Metric).
- Constructions (objects, already applied in Main): `proposition_46`/`46'` (square on a line, 5-tuple),
  `proposition_31` (parallel), `intersection_lines`, `line_from_points`.
- **Cross-book citations: fully-qualify** — `Elements.Book1.proposition_M` (Book-2 names collide with
  Book-1's short names). `import Book.PropM` (Book 1, flat) / `import Book2.PropM.Main` (Book 2).

## HOW THE DEPENDENCY CHECK WORKS (criterion-3 — YOU must satisfy it; `--all` enforces it)
A sentence's `[Prop.~B.M]` citation must be satisfied one of two ways, and `check_step --dependency`
(instant, no build; also run inside `--check` and `--all`) verifies it by SOURCE REGEX:
- **construction arm** — the cited prop is applied WITH `as` in Main (`euclid_apply (proposition_M …)
  as …`), i.e. it produces objects. This is presence-in-MAIN, not block-scoped (a construction may sit
  earlier than its citing sentence — objects are needed early). This arm is Phase A's job; it's already
  in place when you start proving.
- **proof arm** — the cited prop is `euclid_apply`'d (no `as`) somewhere in the sentence's HELPER CONE
  (`stepN.lean` + its sub-files). So if a sentence cites a NON-construction prop, your backing file (or
  one of its sub-files) MUST `euclid_apply (proposition_M …)` it.
**The trap that bit Prop03 step3:** a helper that merely REPACKAGES facts (`exact ⟨h1, h2⟩`) or proves
the claim WITHOUT citing the prop fails the proof arm. If the sentence cites `[Prop.~B.M]` and it's not a
construction, you must actually `euclid_apply (proposition_M …)` in the cone — never term-mode
`:= by exact proposition_M …` (bypasses recording), never just assert the conclusion.
**`check_step --dependency` is NUMBER-ONLY (fast, offline). The HUMAN runs the authoritative BOOK-AWARE
olean check (`check_faithful.sh`) at gate C — do NOT game the regex** (e.g. citing a same-numbered prop
from the wrong book passes the regex but FAILS the human's olean gate). Run `--dependency` to isolate a
criterion-3 problem fast before the slow `--all`.

The olean mechanism (gate C): a citation resolves iff some `proposition_*` in the **transitive dependency
closure** of a constant `euclid_apply`'d in that sentence's block resolves to Book B's prop M — at any
depth, by compiler identity. The script wires each sentence as `euclid_apply (helper_<book>_<prop>_stepN
…)`, and the olean checker follows the closure INTO `stepN.lean` (and its sub-files). This is why the
proof arm works: a prop cited via `euclid_apply` inside your backing file counts.

---

## THE FILE STRUCTURE (where backing/sub files go)
- One Euclid sentence = one `Book<N>/PropNN/stepN.lean` (theorem `helper_<book>_<prop>_stepN`). NEVER inline a
  sentence's proof into Main, never merge two sentences — each must build in isolation.
- A hard step decomposes into more files (never fewer):
  - a few subs → flat in the prop folder: `Book<N>/PropNN/stepN_<sub>.lean` (module
    `Book<N>.PropNN.stepN_<sub>`, theorem `helper_<book>_<prop>_stepN_<sub>`), referenced as a `have stepN_<sub>`
    node inside `stepN.lean` — the script wires + imports it. NEVER a hand-written
    `euclid_apply (helper_…)` + manual import; every helper call is a node.
  - a MASSIVE step with many subs → its own subfolder `Book<N>/PropNN/stepN/<sub>.lean` (module
    `Book<N>.PropNN.stepN.<sub>`), with the step lemma at `Book<N>/PropNN/stepN/Main.lean`. Lake's
    prefix rule builds these with no lakefile change.
- Everything stays in the prop's folder tree. NO `Scratch/`, no merge step. The `check_step.py`
  scripts discover every file automatically.

---

## RESUMING A PROOF (picking up a prop whose state you don't know)
1. Run `check_step Book<N>/PropNN --check` first — instant, no build. It scans naming law / stray sorries
   / dead files up front, so you clean obvious clutter before sinking hours into the next step.
2. Run `check_step Book<N>/PropNN --all` ONCE, backgrounded. This is the one time `--all` is a STARTING
   point rather than the final witness: it walks bottom-up and reports the first node that breaks. Every
   node before the break is already proven — that break is where you resume. (A break on a dead leftover
   file is not a real failure: nothing live references it, so delete it and continue.)
3. From then on, NEVER run `--all` again this session. Resume work at the breaking node and drive with
   scoped `check_step <node>` / `check_step --subtree <node>`, exactly as in a fresh proof. The certainty
   model holds: a cone you don't touch stays proven.

Why `--all` here and not a manual `--subtree` walk: finding the break by hand means enumerating Main's
nodes and running/interpreting many commands — that is agent cognition, the expensive resource. `--all`
is one command: free build time, almost no thinking, and a complete answer including the first break and
any dead files. You pay wall-clock (hours, backgrounded) to save the thing that actually costs.

## THE LOOP IN PRACTICE (per prop) — STRICT, BOTTOM-UP, `--all` AT THE VERY END (and, when resuming, once at the start)
Three commands, three scopes — know exactly what each certifies:
- **`check_step <node>`** = ONLY that node (its SF→SP→P). It does **NOT** check the node's sub-nodes.
- **`check_step --subtree <node>`** = that node's WHOLE CONE (the node + every sub-node it transitively
  contains), bottom-up, scoped to the cone (a shared helper is checked only at its in-cone call sites).
  It does NOT touch other steps. This is how you CONFIRM a container/step is fully done.
- **`check_step --all`** = the WHOLE prop. The FINAL gate, run exactly ONCE.

The ladder (do them in this order):
1. (anytime, free) `check_step Book<N>/PropNN --check` — instant no-build scan: naming law, every node
   has a backing file, every file capped at 30s, nothing pre-wired, no stray sorry.
2. **Decompose + certify LEAVES first.** Build each sentence's backing file, recursing into
   `have`+sub-files until ≤30s. For every LEAF, `check_step <leaf>` until SF+SP+P pass. SF/SP run
   before you prove (so you never sink effort into a bad claim/signature). ONE node at a time. ALL
   builds go through `check_step` (raw `lake`/`safe_build` hard-denied).
3. **Certify each CONTAINER bottom-up, then `--subtree` it — ONLY after its components individually
   pass.** Inner container first (`check_step step27_decomp`), then once its leaves + it are green,
   `check_step --subtree step27` to CONFIRM the whole cone (SP at every in-cone call site + P every
   leaf). A bare `check_step step27` PASS does NOT mean its subtree is done — `--subtree` does.
4. **Certify the steps IN ORDER (step1, then step2, …, then the last; never skip, never parallel).**
   A step is not finished by one `--subtree` on its sentence. To finish a step, run `--subtree` on the
   step's sentence AND on every `have` that belongs to that step's block (the sibling haves passed into
   the sentence as hypotheses). When all of those pass, that step is DONE. Then move to the next step and
   do the same — its sentence and every have in its block. `--subtree <node>` audits only that node's
   cone, so finishing one step never re-audits the earlier steps.
   Why every node and not just the sentence: a sentence is handed its sibling haves as hypotheses.
   `--subtree` on the sentence confirms those hypotheses are PRESENT, but it does not PROVE them — each
   sibling have is proven by its own `--subtree`. So a step is sound only once its sentence and all the
   haves in its block have each passed `--subtree`.
5. **LAST ACTION, exactly ONCE, only once every cone is already `--subtree`-green:** `check_step
   Book<N>/PropNN --all`, launched with `run_in_background: true` (it's 2.5–7 hr — see the anti-pattern
   block; it is a WITNESS you record, not a gate you debug toward). Exit 0 ⟹ the Phase-C wired build is
   GUARANTEED green AND sorry-free. Then delete any `-- dev:` notes from backing files and STOP — hand
   to the human for gate B + Phase C. Do NOT run `wire_main.py` yourself.

> **❌ ANTI-PATTERN — `--all` IS NOT A CHECK. It is a WITNESS that must NEVER, EVER FAIL.**
> Internalize this or you WILL waste hours: `--all` re-walks every node across every call-site — 2.5–7
> HOURS. You run it EXACTLY ONCE, only when you are ALREADY CERTAIN it passes, purely to record the
> green witness for the human's gate B. If there is ANY chance it fails, you are not ready to run it.
> "I edited some cones, let me run `--all` to confirm" is THE forbidden move — that is using a 7-hour
> job as a debug check, and the transcript that motivated this rule did exactly that and burned the time.
> **The ONE exception is RESUMING a proof whose state you don't know** (see RESUMING): there you may run
> `--all` ONCE as a starting snapshot to locate the first break, BECAUSE you have no scoped knowledge to
> target yet. That is still "exactly once" — once you've found the break you NEVER run `--all` again that
> session; you switch to scoped checks. Running it once at the start (resume) and running it once at the
> end (witness) are the only two `--all` runs that ever happen.
>   - **To FIND or CONFIRM-AFTER-A-FIX a failure: scoped checks ONLY.** `check_step <node>` (one node),
>     or `check_step --subtree <node>` (one cone — what `--all` checks, restricted to that cone). A
>     `--subtree` PASS on a cone is a COMPLETE, stand-alone certificate for that cone; it does not need
>     an `--all` to "really confirm" it.
>   - **AFTER ANY EDIT: re-`--subtree` ONLY the cone(s) whose files you touched, then move on.** Do NOT
>     follow edits with an `--all`. The certainty model is COMPOSITIONAL: an unedited cone that passed
>     `--subtree` STAYS passed (its files didn't change). So once every edited cone is `--subtree`-green
>     and `--check`/`--dependency` are clean, Phase B is DONE — the final `--all` is a formality you may
>     even hand to the human, not a gate you must personally re-clear. Never re-verify unedited cones.
>   - **A bare-node PASS is NOT a subtree PASS** — confirm a container/step with `--subtree`.
>   - **Watching a backgrounded `--subtree`/`--all`: poll the JOB'S OUTPUT via the task tools** (it
>     line-buffers a `✓ <node>` feed) — NEVER `sleep N; tail …` / `sleep N; echo done` / `ps`/`grep` on
>     the process. Those foreground spin-waits block the turn AND are blocked by the bash-hygiene hook.
>     There is NO `.lake/.../<node>.log.json` progress file — don't look for one. If the job output isn't
>     pollable in your harness, just wait for the completion ping; never invent a shell workaround.

---

## EXIT PHASE B — what "done" means
Done ⟺ every cone is `--subtree`-green and `--check`/`--dependency` are clean — at which point a final
`--all` is GUARANTEED to exit 0 (it checks nothing a passed `--subtree` of every cone didn't already
check). Run that `--all` ONCE as the recorded witness — or hand it to the human — but it is the
consequence of being done, NOT the way you become done or debug toward done (see the anti-pattern
block). What `--all` certifies, for every node, is exactly what guarantees the final wired build is
green + sorry-free:
- **SP ✓ for every node** — wiring `euclid_apply (helper… (by assumption)…)` at its call site builds:
  every hypothesis is present (discharged by `assumption`, no SMT). SP wires ONLY this node and stubs
  the container's trailing tactics to `sorry`, so it checks hypothesis presence and NOTHING ELSE — it
  does not run the glue;
- **the container build ✓ for every CONTAINER** — building the container with its sub-`have`s as `sorry`
  (sorries tolerated) and its REAL trailing tactics present: the `linarith [...]`/`euclid_finish` after
  the `have`s must close the container's goal from the sub-node claim TYPES (the SF-side build — the same
  one SF runs on a sub-node, since that sub-node's container IS this file);
- **P ✓ for every LEAF** backing file — it builds in isolation, ZERO sorry;
- **no stray sorry** anywhere (the `--check` source scan) — the only `sorry`s are declared node bodies;
- **criterion-3 deps ✓** — every cited `[Prop.~B.M]` is satisfied by a Main construction (`… as …`) or
  its sentence's helper cone (`--all` runs `--dependency`; isolate it fast with `check_step --dependency`
  before the slow `--all`). NUMBER-ONLY — the human's gate-C olean check is the book-aware authority.
The certainty rests on **context-identity**: a `have name : claim := <body>` contributes `name : claim`
to every later tactic's context whether `<body>` is `sorry`, a wire, or a finished proof — so each
node's context in its per-node SP build, and each container's context in its trailing-tactics build, is
IDENTICAL to that context in the final all-wired build. Thus the checks compose: `--all` green ⟹ the
final fully-wired build discharges every wire (deterministic type-match, no search) AND every trailing
tactic closes, with ZERO holes.
**P is LEAF-ONLY.** A CONTAINER backing file (one that has its own `have` sub-nodes) is NEVER built to
"prove" it — that would be redundant: its trailing-tactic SMT (the `euclid_finish`/`linarith` above its
sub-nodes) is certified by the container build above (sub-`have`s `sorry`, real tail present), and its
sub-nodes by their own SP + P. `--all` shows containers as "SP[isolated] + Combine (container)" (Combine
= that trailing-tactics build), leaves as "SP + P". This is why a legit multi-sub-node container (e.g.
`step27_decomp`) is NOT false-flagged as ">30s, decompose".
Then STOP. Phase C is mechanical (the human runs `wire_main.py` + `check_faithful.sh` + the guards); it
is NOT a skill and you do not perform it.

## INTEGRITY
- NEVER fake it (prove-euclid rules): no `sorry`/`admit`/`native_decide`/`axiom` in a finished backing
  file; "it builds" with a sorry warning ≠ proved (`check_step` catches it — a leaf with sorry FAILS P).
- NEVER hand-write wiring or `trace_state` into any file — the scripts own those (and revert them). If
  you ever see a stray `euclid_apply (helper…)` or `trace_state` left in a file, a script was
  interrupted; re-run it or restore the file.
- Don't change a `step_n` CLAIM TYPE (guarded by `check_steps.py`) or a `proposition_*` statement
  (guarded by `check_signatures.py`). If a claim itself is wrong/unprovable, STOP — it's a Phase-A
  error; tell the human.