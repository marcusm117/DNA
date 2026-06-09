---
name: prove-euclid
description: >
  Prove or repair a LeanEuclid / System E proof (Book 1, Book 2 of Euclid's Elements,
  in LeanEuclidPlus). Use whenever a euclid_finish / euclid_assert times out or "Could not
  prove", when filling a sorry in a PropNN.lean / HelperNN_*.lean, or when formalizing a new
  proposition. This skill encodes a decision procedure that prevents the slow "restate-and-hope"
  thrashing that wastes hours; follow it from the first hard step, not after getting stuck.
---

# Proving Euclid in System E — methodology

System E proofs are checked by an SMT backend behind `euclid_finish` / `euclid_assert` /
`euclid_apply`. The hard truth that governs everything below:

> **`euclid_finish` is a fast *checker of small explicit steps*, NOT an oracle that finds proofs.**
> When it is handed a large context or a goal that needs a non-obvious chain, it does not "think
> harder" — it searches, stalls, and times out. **You are the prover. The solver only checks.**

Every rule here is a corollary of that inversion. This methodology was derived the hard way
(Prop 45/47/48); following it from the start turns a multi-hour thrash into steady, fast progress.

The reference example of a *finished, faithful* proof is
[Book2/Prop01.lean](../../LeanEuclidPlus/Book2/Prop01.lean) — read it before starting. It shows
the STAGE-A decomposition comment block + per-sentence `euclid_sentence` `have`s. This skill is
the **how**: how to produce that structure and then discharge each step without thrashing.

---

## ENVIRONMENT

- **Work from the `LeanEuclidPlus/` directory** (`<repo>/LeanEuclidPlus/`). All `scripts/...` paths
  and `lake` targets below are relative to it. `Book/` = Book 1, `Book2/` = Book 2.
- **`euclid_finish` shells out to the SMT solvers `z3` and `cvc5` by bare name** — they MUST be on
  PATH or every proof build fails with `FileNotFoundError: 'z3'`. They live only in the project venv
  `~/.venvs/leaneuclid/bin`. **You do NOT need to `source` anything**: `scripts/safe_build.sh`
  prepends that venv's bin to PATH itself, so just call it bare and z3/cvc5 are found. (If you ever
  invoke `lake build` directly — don't, but if — you would need the venv bin on PATH yourself.)
- **Build ONLY via `scripts/safe_build.sh <Target>`** — never bare `lake build` (see the BUILDING
  section for why: concurrent agents + a build lock). Invoke it **bare and alone**:
  `scripts/safe_build.sh Book.HelperNN_<name>`. Do NOT prefix with `source ~/.venvs/... &&` (the
  script handles the solver PATH) and do NOT wrap in `timeout` (cap SMT time inside the file instead
  — see the SMT TIME CAP section). Avoid `| grep`/`| head` pipelines on the build command: a
  piped/chained command is matched as one whole string and will trip the permission prompt even
  though the bare build is allowed. Run it bare and read the output.
- Lean/`lake` themselves are elan-managed (`leanprover/lean4:v4.8.0-rc2` per `lean-toolchain`), on PATH.
- **Faithfulness check** `scripts/check_faithful.py "Book2/PropNN.lean"` is pure Python 3 stdlib —
  no venv. The book-aware variant `scripts/check_faithful.sh Book2` needs a built `.olean` first.
- The venv `~/.venvs/leaneuclid` also serves the autoformalization pipeline
  (`AutoFormalization/`); activate it explicitly only when running that pipeline tooling.

---

## NEVER FAKE IT (integrity — read first)

A green build that hides a hole is **worse than an honest failure**, because the human trusts "it
builds." These are absolute:

- **Never leave `sorry`, `admit`, `sorryAx`, or `native_decide` in a finished proof, and never
  declare a hard fact as an `axiom` to make the build pass.** `lake build` prints "Build completed
  successfully" *even with `sorry` warnings* — so "it builds" is NOT proof. After any build, check
  the output for `sorry`/`warning` and for `declaration uses 'sorry'`. **Success = zero sorry, zero
  errors.** Report honestly: if a `sorry` remains, the step is NOT done — say so.
- **Never alter a proposition's STATEMENT** (its `theorem proposition_N : ∀ … → …` signature) to
  make it provable. The statement is ground truth (and is statement-faithfulness-checked). Weakening
  a hypothesis or the goal is a silent correctness/faithfulness break. Only the **proof body** and
  **helper lemmas** may change. (Helper lemmas you create may take tailored hypotheses — that's fine;
  the *proposition's own* signature is sacred.)
- **Derive, don't axiomatize.** If a needed fact follows from existing axioms / earlier propositions,
  DERIVE it (that is the whole job — see the pattern gallery). The bar for interrupting the human is
  high: stop and ask **only** if (a) you become convinced the goal/sub-fact is actually FALSE, or
  (b) you are convinced a genuinely NEW axiom (not in `SystemE/Theory/`) is required. Do not ask the
  human just because a step is hard — hard-but-derivable is the normal case; do the derivation.
- **Touch only the proposition the human assigned you.** If a *different* prop is broken, REPORT it;
  do not "helpfully" fix it (another agent may own it).

## THE NON-NEGOTIABLE RULES

Violating any of these is what causes the thrash. They are hard constraints, not suggestions.

0. **STRUCTURE FIRST — never one-shot the proof.** Do NOT write the whole proof and run it to "see
   if it works." A failing all-in-one `euclid_finish` teaches you almost nothing and burns a build.
   Before any proof tactic: decompose the Euclid argument into a justified step-structure (Phase 1
   below, format = [Book2/Prop01.lean](../../LeanEuclidPlus/Book2/Prop01.lean)), stub each step with
   `sorry`, confirm the SKELETON elaborates, and only THEN discharge leaves one at a time (Phase 2 =
   THE LOOP). The shape of the work is always: **decompose → justify → stub → confirm skeleton →
   fill leaves**, never "attempt → fail → patch."

1. **Never run a tactic you cannot justify.** Before any `euclid_finish`/`euclid_apply`, you must
   be able to say *why* it closes (which axioms, which facts). If your reason is "let's see" or
   "I believe it should" — STOP. "I believe" = "not verified" = not done.

2. **Never run something you predict will fail or be slow.** If you suspect a step won't close,
   that suspicion is information: act on it (decompose / find the right axiom) instead of running it.

3. **The 30-second rule.** If a single `euclid_finish` takes more than ~30s, it is too big.
   Do NOT wait it out or retry verbatim. Decompose into smaller `have`s. Speed is the signal:
   a correct atomic step is fast; a slow step means you are asking the solver to search.

4. **One lemma per file; prove one at a time.** Never bundle multiple unproven helpers into one
   file "to test together." Smallest verifiable unit, isolated, built on its own.

5. **Reason before building. Builds confirm; they never substitute for thinking.** A full Prop
   build can be minutes (Prop47 ≈ 10 min). Never build "to see what happens." Build only to
   *confirm* something you already have strong reason to believe. Cheap isolated helper builds
   (`import SystemE` only, ~30s) are fine and encouraged as confirmation.

6. **Decompose only into ENTAILED sub-facts.** A `have hX : P := by ...` is a bug, not progress,
   if `P` is not actually forced by the current hypotheses. The classic trap: splitting a true
   goal into a sub-fact that is only *sometimes* true (e.g. holds when an angle is acute, but the
   context doesn't pin acuteness). Such a `have` can never close and wastes every cycle. Before
   introducing a sub-fact, confirm the context entails it.

7. **Verify TRUTH on a concrete model before proving.** When a fact's truth is in doubt, assign
   coordinates that satisfy THIS proposition's hypotheses and check numerically. Pick the model to
   fit the prop — a right-triangle prop might use a=(0,0), b=(0,3), c=(4,0); a general-triangle prop
   needs a generic (non-right, non-isoceles) triangle so you don't accidentally rely on a special
   case. A statement can be true yet your *decomposition* of it false — distinguish these.

8. **Replace SMT search with explicit axiom application.** The single most effective move. Instead
   of hoping `euclid_finish` finds the chain, apply the axioms yourself with `euclid_apply`, so the
   solver has nothing to search. (See the pattern gallery.)

9. **Check axioms and context YOURSELF.** Read the axiom signature; map each of its preconditions
   to a named fact in the goal state. Do not ask the human to read the info view for something you
   can derive, and do not guess argument order — look it up.

---

## PHASE 1 — STRUCTURE FIRST (do this before ANY proof tactic)

This is how every proof BEGINS — whether formalizing a new proposition or repairing one. It is the
discipline that prevents the wasteful "write it all, run it, watch it fail" start.

```
1. READ THE SOURCE. The Euclid proof text (Book{N}/texts_proofs/{prop}.txt) and the reference
   format Book2/Prop01.lean. Understand the mathematical argument before formalizing.

2. DECOMPOSE (STAGE-A). Write the numbered step-structure as a comment block, exactly like
   Prop01's STAGE-A: each step has objects / hypotheses / WTS (what-to-show) / reasoning /
   DEPENDS-on-which-earlier-steps. This is where you JUSTIFY the structure — each step must follow
   from its named dependencies. If a step doesn't follow, the decomposition is wrong; fix it here,
   on paper, where it is cheap — NOT later by patching tactics.

3. STUB AS A SKELETON. Encode each step as a `have`/`euclid_sentence` (Book 2: use the faithfulness
   annotations per Book2/WORKFLOW.md) with `:= by sorry`. Constructions become `euclid_apply ... as x`.
   The conclusion chains the step results.

4. CONFIRM THE SKELETON ELABORATES. Build with the `sorry`s in place. This checks the STRUCTURE is
   type-correct (every step's statement is well-formed, dependencies are in scope) before you spend
   any effort proving leaves. A skeleton that elaborates = a correct plan; now the work is only to
   fill `sorry`s — and filling a `sorry` can never invalidate the structure.
```

A `sorry`-stubbed skeleton that builds is REAL, durable progress. One-shotting is not. Only after
the skeleton elaborates do you enter Phase 2 to discharge each leaf.

## PHASE 2 — THE LOOP (discharge one `sorry` / failing step at a time)

```
1. GET THE GOAL STATE. Put a `sorry` at the failing point; read the info-view context
   (or ask the human to paste it). You need: the exact goal, and every named hypothesis.

2. ISOLATE THE ONE FAILING GOAL. A timeout at the end of a long proof is almost always
   "huge context", not "hard logic". Identify the single conjunct/assert that fails.

3. TRIM TO A HELPER LEMMA. Create Book/HelperNN_<name>.lean with `import SystemE` (+ only the
   PropNN it truly needs). State the failing goal as a theorem whose hypotheses are ONLY the
   facts relevant to it, copied from the goal state. ~10 facts, not ~60. This alone fixes most
   timeouts (smaller context = no search blowup).

4. TRACE THE PROOF BY HAND. Decide the axiom chain. For each `euclid_apply (axiom args)`:
     - read the axiom's signature (grep SystemE/Theory/Inferences/*.lean),
     - map every argument and every PRECONDITION to a fact you have,
     - if a precondition isn't present, that's your next sub-goal (recurse).
   Prefer explicit axiom applications over `euclid_finish` for anything non-trivial.

5. BUILD THE HELPER (cheap, ~30s). `scripts/safe_build.sh Book.HelperNN_<name>`.
   If a step is slow (>30s) or fails: it's too big or not entailed — go to 4 and decompose.

6. WIRE INTO THE PROP. Add the import; replace the failing line with
   `euclid_apply (helper... args)`. The call site must discharge the helper's hypotheses — verify
   EACH helper hypothesis is a NAMED fact in the Prop's context (from the dump), or is cheaply
   derivable there. If a hypothesis isn't available, you've moved the problem, not solved it:
   either narrow the helper's hypotheses to context-present facts, or derive the missing one
   explicitly in the Prop first.

7. CONFIRM with one build of the Prop. "Build completed successfully" is necessary but NOT
   sufficient — also confirm NO `sorry`/`declaration uses 'sorry'` warnings remain (grep the source
   and the build output). Zero sorry + zero errors = done; anything less is not.
```

---

## CRUCIAL SUBTLETIES (learned painfully — don't relearn them)

### Construction data is NOT re-derivable from a trimmed context
Facts like `d.sameSide c AB` (which side of a line a constructed point lands on) come from the
*construction* (e.g. `proposition_46'` building a square on a chosen side). They are NOT logically
entailed by incidence + distinctness alone. If your helper needs such a fact:
  - first check if the Prop **already has it named** in context (it often does — pass it in as a
    helper hypothesis, and it discharges trivially at the call site); 
  - if the Prop does NOT have it named, you must DERIVE it (it is not free), or realize your
    decomposition is wrong.

### `euclid_apply` adds the CONCLUSION, not the preconditions
When you `euclid_apply (some_axiom ...)`, the solver discharges the axiom's antecedent and adds
its **conclusion** to context. The antecedent conjuncts are proved transiently and are **NOT**
left as hypotheses. So you cannot rely on "prop29 used `f.opposingSides l GH` at line 32, therefore
it's in context at line 38" — it is not. If you need it later, derive/assert it where needed.

### Circularity in angle/side reasoning
`sum_angles_onlyif` produces an angle-sum equation FROM two `sameSide` facts; `sum_angles_if`
produces the `sameSide` facts FROM the angle-sum. So proving a `sameSide` via an angle-split that
itself needs that `sameSide` is circular. Break circularity with a *different* primitive —
typically **betweenness → sameSide via `pasch_2`/`pasch_4`** (which don't go through angles).

### A discharged precondition of an earlier `euclid_apply` is a real, true fact
If `proposition_31 a b d BD` was applied successfully, its precondition `¬a.onLine BD` was true
there. That tells you the fact is PROVABLE (good for designing a derivation) — but per the rule
above it is not necessarily still *in context*. Re-derive it explicitly if a later step needs it.

---

## PATTERN GALLERY (reusable explicit-axiom chains)

These are the moves that replaced `euclid_finish`-and-hope. Grep the axiom file for exact sigs:
`SystemE/Theory/Inferences/{Diagrammatic,Transfer,Metric}.lean`.

- **Point on opposite sides of a line ⟹ betweenness.** `pasch_4 a b c L M`: `L≠M`, `b∈L∩M`,
  `a,c` distinct on `M`, `¬a.sameSide c L` ⟹ `between a b c`. Use to prove a transversal foot
  lands between two points. (Prop47 `between b l' c`; Prop45 glue points.)

- **Betweenness ⟹ the two sameSide facts ⟹ angle split.** `pasch_2` turns `between p x q` into
  `x.sameSide ... `; then `sum_angles_onlyif` turns those into `∠p:b:q = ∠p:b:x + ∠x:b:q`.
  This is the NON-circular way to split an angle at an external point. (Prop47 perpendicular lemma.)

- **Three lines through one point — side transfer.** `triple_incidence_2 L M N a b c d`: from one
  `sameSide` + one `¬sameSide` across the three concurrent lines, derive a third `sameSide`.
  (Prop47 `f.sameSide a BC` from `a.sameSide c BF`.)

- **Parallel ⟹ same side / off-line.** `intersection_lines_opposing` (contrapositive): points on a
  line that does NOT cross `L` are on the same side of `L`. `intersection_lines_common_point`: a
  point on two distinct lines ⟹ they intersect (use by_contra to prove a point is off a parallel).
  (Prop45 `l.sameSide m GH`.)

- **Parallels + transversal ⟹ equal/right angle.** `proposition_29'''` (alternate angles): for
  `AL ∥ BD` cut by transversal, `∠a:l':b = ∠l':b:d`; combine with a known right angle to get
  AL ⊥ transversal. (Prop47 `helper_47_AL_perp_BC`.)

- **Area decomposition of a glued parallelogram.** `sum_parallelograms_area a b c d e f ...`:
  with `e` between `a,b` and `f` between `c,d`, the four sub-triangles sum to the two halves.
  One apply + linear arithmetic closes area-sum goals. (Prop45 `helper_45_area_sum`.)

- **Right-triangle / Pythagoras length algebra.** Pure `|·|` equations: substitute and use
  `s² = t², s,t ≥ 0 ⟹ s = t` (the solver knows `segment_gte_zero`). No geometry needed — strip
  the helper to just the length equations. (Prop48 `helper_48_dc_eq_bc`.)

- **Acute/obtuse case splits.** `between_points` gives the 3 orderings of collinear points;
  rule out the bad ones with `proposition_13` (straight-line supplement = 2∟) + `proposition_17`
  (triangle angle bound) + an acuteness fact. `euclid_finish` will NOT do this case-split for you.
  (Prop47 `helper_47_between_blc`.)

---

## SMT TIME CAP — fail fast, don't burn the default 300s

`euclid_finish` gives each solver a **default of 300 seconds** (`systemE.solverTime`). That is why a
single bad/too-big step can hang for minutes before failing — the opposite of the 30-second rule.

**While developing a helper, cap it to 30s so over-large steps fail fast** instead of stalling. Put
this immediately above the theorem (it applies to the next declaration):

```lean
set_option systemE.solverTime 30 in
theorem helper_NN_<name> : ... := by
  ...
```

A step that can't close in 30s is telling you it's too big or not entailed — decompose it (Phase 2),
don't raise the cap to wait it out. Do NOT use a shell `timeout` around the build for this — the cap
belongs in the file, where it actually bounds each solver call.

Once the helper is proven: a well-decomposed step closes in well under 30s, so the cap usually just
stays (harmless). Only if a *legitimate, irreducible* step genuinely needs more should you raise or
remove the cap — and then say so, because a committed proof relying on a near-300s solve is fragile.
Never raise the cap merely to make a thrashing step pass.

## BUILDING — always go through `safe_build.sh`

**Always build with `scripts/safe_build.sh <Target>`, NEVER bare `lake build`.** Multiple agents
edit and build different files concurrently; `safe_build.sh` holds an exclusive `flock` so only one
`lake build` runs at a time. Bare `lake build` from two agents at once corrupts `.lake/build/` and
Lake's trace DB, which breaks the build for everyone. This is a correctness requirement, not a
convenience.

```bash
scripts/safe_build.sh Book.HelperNN_<name>      # cheap isolated helper, ~30s — build freely to confirm
scripts/safe_build.sh Book.PropNN               # heavier; some (e.g. Prop47) ~10 min — build only to CONFIRM
scripts/safe_build.sh Book.A Book.B             # multiple targets ok
```

Exit code is lake's, so you can branch on success/failure. Per Rule 5: cheap helper builds are for
confirmation and encouraged; expensive Prop builds are never for exploration.

## WORKING ALONGSIDE OTHER AGENTS

- **Other agents may be editing other Prop/Helper files in this repo at the same time.** Touch only
  the files for YOUR assigned proposition (its `PropNN.lean` and the `HelperNN_*.lean` you create).
  Do not edit another proposition's files or another agent's helpers.
- **Do not run `git` mutations** (`add`, `commit`, `push`, `restore`, `checkout`, `stash`). The human
  owns git. The last commit is the human's safety net — they can revert anything you change — which
  is exactly why git stays in their hands. Read-only git (`status`, `diff`, `log`) is fine.
- You MAY freely create/edit files under `Book/` and `Book2/` (permission is granted) — the git
  safety net makes that safe. Just stay within your proposition's files.

## HELPER FILE CONVENTIONS

- Name `Book/HelperNN_<short_name>.lean`; theorem `helper_NN_<short_name>`; `namespace Elements.Book1`
  (or `Book2`). Doc comment: which Prop line it serves, the NL geometry, and the proof strategy.
- Import only what's needed (`SystemE` + specific `Book.PropMM`). Keeps builds fast.
- Hypotheses = exactly the facts the proof uses, copied from the goal-state dump. No more, no less.
- While developing, put `set_option systemE.solverTime 30 in` above the theorem (fail-fast cap).
- After proving, wire into the Prop with a single `euclid_apply`; the original proof body stays clean.

## DON'T

- Don't add a hypothesis to a helper to make it close without checking the Prop can supply it
  (you've only moved the problem — see Phase 2 step 6).
- Don't change PropNN's overall proof structure to patch one step — extract a helper instead.
- Don't report "done / it builds" while a `sorry` remains (see NEVER FAKE IT).

**Note for the human committer (not the agent — agents don't run git):** when committing Book work,
`git add Book/` alone is insufficient. Book depends on `SystemE/` (the faithfulness tactics:
`Faithful.lean` + changes to `Solve.lean`/`Util.lean`/`Tactics.lean`) and on the `Book.lean` /
`Book2.lean` aggregator import lists. Stage those too, or the build breaks for everyone else.
