---
name: faithful-euclid
description: >
  Make a LeanEuclid / System E proof FAITHFUL — annotate it so it follows Euclid's sentence
  structure and passes the faithfulness criteria (Book 1 / Book 2 of Euclid's Elements, in
  LeanEuclidPlus). Use whenever the task is "make Book2/PropNN faithful", to add
  euclid_intro_sentence / euclid_sentence / euclid_conclude_sentence annotations to a proof, or to
  re-prove a proof so each of Euclid's sentences maps to a checkable step. Each proposition lives in
  its OWN FOLDER `Book<N>/PropNN/` — `Main.lean` (the proposition) plus one `stepN.lean` per sentence.
  This skill owns the phase-gated, per-step-isolated pipeline; it delegates the actual proving to the
  `prove-euclid` skill. Faithfulness is NOT a refactor of the existing proof — expect to re-prove.
---

# Making Euclid proofs FAITHFUL — methodology

A proof can **compile** and still be **unfaithful**: the existing Book 2 proofs lean on
constructions and facts Euclid never had. Making a proof faithful means re-expressing it so it
follows Euclid's own sentence structure — usually **re-proving**, not refactoring. The only trusted
ground truth at this stage is the **statement** (`theorem proposition_N : ∀ … → …`); everything in
the proof body is up for grabs.

> **READ `prove-euclid` FIRST — it is a hard prerequisite.** This skill is the *faithfulness layer*:
> it owns the phases, the sentence mapping, the step-file conventions, and the integrity rules. All
> *actual proving* (decompose → sorry-skeleton → fill leaves, the pattern gallery, the 30s cap,
> `safe_build.sh`) is `prove-euclid`'s job and is invoked from inside Phase B here.

## FILE LAYOUT — one folder per proposition (READ THIS; it shapes everything)

Each proposition is a **folder** `Book<N>/PropNN/`:
```
Book2/Prop02/Main.lean    module Book2.Prop02.Main   -- the proposition + its euclid_sentences
Book2/Prop02/step1.lean   module Book2.Prop02.step1  -- theorem helper_2_step1  (one per sentence)
Book2/Prop02/step2.lean   ...                        -- + stepN_<sub>.lean for any sub-decomposition
```
- `Main.lean` `import Book2.PropNN.step1 …` and discharges each `euclid_sentence` by
  `euclid_apply (helper_<book>_stepN …)`. The aggregator `Book2.lean` imports `Book2.PropNN.Main`.
- **Build one step alone:** `scripts/safe_build.sh Book2.PropNN.stepN`. Build the prop:
  `scripts/safe_build.sh Book2.PropNN.Main`.
- **Everything for a prop lives in its folder and STAYS.** There is **NO `Scratch/` directory, NO
  `_steps.lean` file, and NO "Phase C reunite/move."** You write step files where they belong from
  the start; Main's skeleton already wires the `euclid_apply` calls, so there is nothing to merge.
- Sub-lemmas a step needs are their **own files in the same folder** with clear names
  (`stepN_<sub>.lean` → theorem `helper_<book>_stepN_<sub>`). Everything separate = easy to debug.
- **Already-done props (Prop01, Prop03–14) are ALREADY relocated** into `PropNN/Main.lean` with their
  existing proofs intact. Making one faithful = add `stepN.lean` files in its folder. Do NOT recreate
  a Scratch dir or a merge step, and touch only YOUR prop's folder.

**On Prop01 — read [Book2/Prop01/Main.lean](../../LeanEuclidPlus/Book2/Prop01/Main.lean) for the
OUTPUT shape only.** Annotated by hand pre-pipeline: monolithic (proofs inline, no `stepN` files). Use
it to see what a finished faithful prop reads like — the `euclid_intro_sentence` / `euclid_sentence` /
`euclid_conclude_sentence` annotations, the locator/text/type shape, and that the file is just
imports → theorem → annotated proof (no header comment block). Do **NOT** copy its inline proving
style — your step proofs live in separate `stepN.lean` files. **`Book2/Prop02/` is the real example**
of finished pipeline output (Main + step1…step6).

---

## WHAT "FAITHFUL" MEANS (the 3 criteria)

Spec: [Book2/faithful.txt](../../LeanEuclidPlus/Book2/faithful.txt). A proof is **proof-faithful** iff:

1. **All sentences present + exact text (machine-checked).** Every one of Euclid's sentences maps to
   an annotation; concatenating the annotation texts in locator order reproduces the canonical source
   `Book<N>/data/texts_proofs/<N>.txt` **character-for-character**. (faithful.txt criterion 1.)
2. **Each step's claim is honest (HUMAN-checked).** Each `euclid_sentence`'s Lean type genuinely
   captures what that Euclid sentence asserts. No machine checks this — which is exactly why faking
   it is the dangerous failure mode (see INTEGRITY). (faithful.txt criterion 2.)
3. **Cited deps are referenced (machine-checked, book-aware).** Every `[Prop.~B.M]` Euclid cites is
   *referenced* (not necessarily proof-of-use) in that sentence's block. (faithful.txt criterion 3.)

**Statement-faithfulness** (the theorem signature matches Euclid's enunciation) is separate and
human-checked; you must NEVER change it. **Compiling** is separate again — that's `lake build`.

### How the dependency check is decided (the capture model — internalize this)

A sentence's **block** = the source from the previous `euclid_sentence` up to and including this one:
the `euclid_apply` constructions before it **and** its own `:= by …` body. A citation `[Prop.~B.M]`
is satisfied iff **some `proposition_*` in the transitive dependency closure of a constant applied
(via `euclid_apply`) in that block resolves to Book B's proposition M** — matched by compiler
constant identity (book-aware), at any call depth ("function inside a function inside a function").

The one mechanical consequence: **a citation is recorded only when the prop/helper enters via
`euclid_apply`.** A construction (`euclid_apply (proposition_11'' …) as f`) is captured because it
runs as an apply; an applied step lemma (`euclid_apply (helper_2_step5 …)`) is captured and the
checker follows its closure (into the `stepN.lean` file) down to the props it uses. **Term-mode
`:= by exact proposition_M …` is NOT captured** — never discharge a cited step that way.

### The two checkers

| Command | Build? | Text | Deps | Use |
|---|---|---|---|---|
| `python3 scripts/check_faithful.py "Book<N>/PropNN/Main.lean"` | no | exact | single-file, number-only, best-effort | fast dev sanity check |
| `scripts/check_faithful.sh Book<N>` | needs built `.olean` | exact | **book-aware, transitive closure** | **authoritative final gate** |

The regex checker reads ONE file's text (`Main.lean`) and cannot follow a `helper_` call into a
`stepN.lean` file, so its dep result is best-effort. **The olean run is the bulletproof authority**:
it follows the transitive closure into the `stepN.lean` files, book-aware. Run from `LeanEuclidPlus/`.

---

## ENVIRONMENT (same as prove-euclid — see it for detail)

- **FIRST THING: `cd` into `LeanEuclidPlus/`.** The Claude session is launched at the repo root
  (`<repo>/DNA/`, where `.claude/settings.json` lives) but ALL paths in this skill — `scripts/…`,
  `Book2/PropNN/Main.lean`, `Book2/PropNN/stepN.lean`, `Book2/data/texts_proofs/N.txt` — are relative to
  `<repo>/LeanEuclidPlus/`, and the permission allow-rules (`Bash(scripts/safe_build.sh:*)`,
  `Bash(python3 scripts/check_*.py:*)`) only match when the command starts with bare `scripts/…`,
  i.e. when run from `LeanEuclidPlus/`. So make your **very first Bash call** a bare `cd LeanEuclidPlus`
  (allowed; the Bash cwd PERSISTS across later calls), then run every command bare from there. Do NOT
  chain `cd … && …` (chained commands trip the prompt) — one standalone `cd` up front, then bare
  commands. (File READS via the Read/Grep tools take repo-root/absolute paths regardless.)
- Work from `<repo>/LeanEuclidPlus/`. `Book/` = Book 1 (FLAT, untouched), `Book2/` = Book 2 (folders).
- Build ONLY via `scripts/safe_build.sh <Target>` (build lock for concurrent agents). Run it **bare**
  — no `timeout`, no pipes (a piped command trips the permission prompt). z3/cvc5 are put on PATH by
  the script; you don't `source` anything.
- Step files live in the prop's own folder `Book<N>/PropNN/stepN.lean` and build in isolation:
  `scripts/safe_build.sh Book<N>.PropNN.stepN`. (No `Scratch/` — that is gone.)
- `lake build Book<N>` then `scripts/check_faithful.sh Book<N>` is the authoritative faithfulness gate.

### Tool hygiene
General tool/shell rules (use Read/Grep not shell, never chain commands, run builds bare) are in
**CLAUDE.md** — follow them; they prevent most wasted turns and permission prompts. Faithfulness-specific:
- **You do NOT need to read `Faithful.lean`** to use the annotation tactics — their exact syntax is in
  this skill and in Prop01. Don't spelunk the tactic implementation.
- Most signature lookups are already in the SYSTEM-E QUICK REFERENCE below; grep the Inferences files
  only for the rest.

---

## SYSTEM-E QUICK REFERENCE (so you don't re-derive the stable surface every prop)

The facts below are stable across ALL books and are the ones agents otherwise waste turns
rediscovering. For anything not here, grep `SystemE/Theory/Inferences/{Metric,Transfer,Diagrammatic}.lean`
and `SystemE/Theory/Relations.lean` — and **add what you learn to this list** when it's reusable.

**Area / rectangle convention (Book 2 is area-heavy):**
- "rectangle contained by X and Y" = `|X| * |Y|` (the length-product). "square on X" = `|X| * |X|`.
  There is **no** square-area axiom — a square is the right-angled parallelogram case of
  `rectangle_area`.
- An "area" of a figure is expressed as a **sum of `Triangle.area △ p:q:r`** terms (the figure split
  into triangles); equalities between figures are linear equations over those triangle areas. See
  Prop01's `step5`/`step6` for the pattern.
- `Triangle.area △` is **permutation-invariant** in its 3 vertices (via `area_symm_1`/`area_symm_2`
  in `Metric.lean`): vertex order is cosmetic for areas, `euclid_finish` reconciles it. (Order DOES
  matter for `between`, `∠`, `formTriangle` — just not for `Triangle.area`.)

**Key area axioms** (`SystemE/Theory/Inferences/Transfer.lean`, grep for exact arg order before use):
- `rectangle_area a b c d AB CD AC BD : formParallelogram a b c d … ∧ ∠a:c:d = ∟ →`
  `(area△a:c:d + area△a:b:d = |a─b|*|a─c|) ∧ (area△b:a:c + area△b:d:c = |a─b|*|a─c|)`
  — turns a right-angled parallelogram's triangle-areas into a length-product (the rectangle = `|X|*|Y|`).
- `parallelogram_area …` — the two diagonals' triangle-area identity for any parallelogram.
- `sum_parallelograms_area a b c d e f … : formParallelogram … ∧ between a e b ∧ between c f d →`
  the 4 sub-triangle areas sum to the 2 half-parallelogram areas (area decomposition of a split
  parallelogram). Used to glue/split rectangles (Prop01 `step5`, Prop45).
- `sum_areas_if/onlyif`, `degenerated_area_*` (Transfer); `area_gte_zero`, `area_symm_1/2`,
  `area_congruence`, `degenerated_area` (`Metric.lean`).

**Constructions that return MANY objects (destructure with a tuple `as (…)`):**
- `proposition_46 a b AB : … → ∃ (d e : Point)(DE AD BE : Line), formParallelogram d e a b DE AB AD BE`
  `∧ |d─e|=|a─b| ∧ |a─d|=|a─b| ∧ |b─e|=|a─b| ∧ (∠b:a:d=∟) ∧ (∠a:d:e=∟) ∧ (∠a:b:e=∟) ∧ (∠b:e:d=∟)`
  — "describe the SQUARE on AB". Apply as `euclid_apply (proposition_46 a b AB) as (d, e, DE, AD, BE)`.
- `proposition_46' a b x AB` — same but on the side **opposite** `x` (adds `d.opposingSides x AB`);
  use when the square must go on a chosen side. (cf. Prop47 for tuple-apply usage.)
- `proposition_31 a b c BC` — line through `a` parallel to `BC` (the "draw parallel" construction).

**Common relation abbrevs** (`SystemE/Theory/Relations.lean`):
- `formParallelogram a b c d AB CD AC BD` — `a,b,c,d` corners with the named side-lines.
- `formTriangle`, `formRectilinearAngle`, `distinctPointsOnLine` — as used throughout the props.

**Imports & cross-book names (read before citing another book's prop):**
- **`import` is mandatory** to use ANY prop from another file — `euclid_apply (… proposition_M …)`
  fails unless that file is imported, even fully-qualified. `import` loads the file; `namespace` only
  decides the name. So `import Book.PropM` (Book 1) / `import Book2.PropM.Main` (Book 2) for each prop
  you cite. (Book 1 is flat: `import Book.PropM`. Book 2 is foldered: `import Book2.PropM.Main`.)
- **The short name collides across books.** Book 1 prop M is `Elements.Book1.proposition_M`; Book 2
  prop M is `Elements.Book2.proposition_M`. Bare `proposition_M` is ambiguous when both are in scope.
- **Convention: fully-qualify cross-book citations.** In a Book-2 proof, write Book-1 citations as
  `Elements.Book1.proposition_M`. Unambiguous, and makes the book-aware checker resolve trivially.

---

## STEP = ONE ISOLATED FILE IN THE PROP FOLDER (non-negotiable)

The whole reason for this structure: **never wait on a giant build to discover a late step broke.**
A 100-step proof rebuilt as one unit costs an hour to find a step-100 failure. Instead:

- Each Euclid sentence is proved in its **own file** `Book<N>/PropNN/stepN.lean`, holding
  `theorem helper_<book>_stepN` (e.g. `Book2/Prop02/step5.lean` → `helper_2_step5`). Builds alone ~30s.
- **Never** name a step THEOREM `proposition_*` (reserved for real Euclid props — a stray
  `proposition_` can mislead the checker); the theorem is `helper_<book>_stepN`, the file `stepN.lean`.
- Sub-decompositions are their own files in the same folder: `stepN_<sub>.lean` → `helper_<book>_stepN_<sub>`.
- A step lemma's **hypotheses** = exactly what it needs: the objects in play, the relevant setup
  hyps, **the conclusions of earlier steps** it uses, and **the conclusion of any prop it cites**
  (passed in as a hypothesis — the lemma proves its claim *from* that, it does not re-derive the
  cited prop). Its **goal** = that sentence's `step_n` type (from the Phase-A contract). No more.
- Redundant hypotheses across step files are FINE — isolation and speed beat DRY here.

---

## PHASE DETECTION

Invoked with a path (`/faithful-euclid Book2/Prop02.lean` or `.../Prop02/Main.lean`). Detect where you
are from `Book<N>/PropNN/Main.lean`:

- **No `euclid_*` annotations in `Main.lean`** → start at **Phase A**.
- **Annotations present, but `stepN.lean` files missing / not all building** → **Phase B**.
- **All `stepN.lean` build + `Main.lean` builds** → **FINAL GATE** (verify + clean up). NO "Phase C
  reunite": Main already calls the steps via `euclid_apply`; the gate is just checks + comment cleanup.

For a future book whose sentences already exist (Books 3/4), you may be handed a prop already past
Phase A — detect and resume at B.

---

## PHASE A — SENTENCE MAP (then STOP for human review)

> ### ⛔ PHASE A — THREE HARD RULES (violating any is the #1 cause of wasted hours)
> **RULE 0 — THE SENTENCE IS THE SOURCE OF THE CLAIM; THE DIAGRAM ONLY RESOLVES LABELS.** A `step_n`
> type is a faithful restatement of WHAT THAT EUCLID SENTENCE SAYS — nothing more, nothing less. The
> diagram is allowed for ONE thing only: resolving a label (which point is `G`; which corners a
> figure-name like "HF" denotes, since Euclid names figures by opposite corners). You may **NOT**
> build a coordinate model of the figure, read geometric facts off the picture, "audit" claims against
> coordinates, or expand one sentence into many facts the sentence didn't state. If Euclid writes one
> sentence "HF is also a square," the claim is ONE assertion about HF (matching how Prop02 `step3`
> types "AE is the square on AB" as a single area equation) — NOT an invented enumeration of four
> sides + four right angles read from the diagram. Formalizing the picture instead of the words is a
> criterion-2 (faithfulness) violation, even when the picture is geometrically true.
>
> **RULE 1 — DO NOT READ ANY AXIOM FILE.** In Phase A you may NOT open or grep
> `SystemE/Theory/Inferences/**` (Transfer / Metric / Diagrammatic), and you may NOT go looking for
> "which axiom proves this." Those files answer HOW to prove a step = **Phase B**. A claim TYPE is
> written from ONLY: the Euclid text, the diagram, the proposition's own signature, and the SYSTEM-E
> QUICK REFERENCE above. If you feel the urge to open an Inferences file, STOP — write the claim type
> and move on. (Reading a construction prop's signature in `Book/` or a relation def in
> `Relations.lean` is fine; the axiom/Inferences files are not.)
>
> **RULE 2 — WORK A FEW SENTENCES AT A TIME, NOT THE WHOLE FILE.** Do NOT design all claim types in one
> giant think. Take a small CHUNK (you pick the size — e.g. 3–6 related sentences), write their claim
> types + any constructions, BUILD to confirm they elaborate, then move to the next chunk. A long
> single think over all sentences is the failure mode — chunking keeps each step cheap and verifiable.
>
> These are not suggestions. If you find yourself reading axioms, planning the whole proof in one
> shot, or writing facts off the diagram that the sentence didn't state, you have left Phase A's lane.

Goal: pin down, for every Euclid sentence, its locator, verbatim text, and the **Lean type of its
claim** — and prove the *skeleton* type-checks. No real proving yet. All of this is in `Main.lean`.

> **SCOPE FENCE — READ BEFORE YOU START.** Phase A produces only the sentence *claims* (the `step_n`
> types) — WHAT each sentence asserts, not HOW to prove it. **Do NOT research proof strategy here:**
> no grepping area axioms, no checking `Triangle.area` permutation/symmetry, no studying how another
> prop discharged a step, no reading axiom signatures to plan tactics. ALL of that is **Phase B**,
> done later, per-step, in the `stepN.lean` files. If you catch yourself opening
> `SystemE/Theory/Inferences/*` or asking "which axiom proves this?", **STOP — that's Phase B; you've
> left Phase A's lane.** To write a `step_n` type you only need (a) the Euclid text and (b) the
> existing theorem's statement vocabulary (the `|·|`, `∠`, `Triangle.area`, `between`, etc. already in
> the prop's signature and in Prop01). That's it. A `sorry` stands in for every proof in this phase.
>
> **Effort:** medium is plenty for Phase A (it's text-slicing + type-writing, not hard reasoning).
> Save high effort for Phase B, where the actual proving happens. (Effort is a session setting — the
> human sets it; this is just guidance on what the phase needs.)

Phase A is split into **A1 (text split — fast)** and **A2 (claim types — one sentence at a time)**.
Do A1 fully first; it is mechanical and should take minutes, not a long think.

### A1 — split the text into sentences (NO Lean types yet)

> **WIPE THE OLD PROOF FIRST (mandatory).** `Main.lean` already compiles with an UNFAITHFUL proof.
> Before anything else, **delete the entire existing proof body** — everything AFTER `:= by` down to
> just `euclid_intros` — and build the faithful proof FRESH from the sentence skeleton. Do NOT keep
> the old tactics around and try to make them faithful, and do NOT reuse leftover `have`s.
> **Do NOT touch the signature** (`theorem proposition_N : ∀ … → … :=`): leave those lines exactly as
> they are — don't edit, reformat, or even retype them. The signature is ground truth and is checked
> independently (`scripts/check_signatures.py`); any change to it is a hard failure. Edit ONLY the body.
>
> **NEVER "just close the goal."** A faithful proof is built ONLY from the per-sentence
> `euclid_sentence` steps and their `euclid_apply`s. You may NOT discharge the proposition's goal (or
> any step) with a leftover bulk tactic — **no `linarith`/`nlinarith`/`ring`/`simp`/`omega`/big
> `euclid_finish` over the whole goal** carried over from the old proof. If a build is green but the
> goal was closed by anything other than the faithful step chain, that is a FAITHFULNESS FAILURE.
> (Pure length/area *algebra* may still go inside a specific `stepN.lean`'s proof — but it realizes
> that sentence's claim; it is never a catch-all goal-closer in Main.)

**Per-proposition resources** (keyed by the prop NUMBER `<N>`, relative to `LeanEuclidPlus/`):
- `Book<N>/data/texts_proofs/<N>.txt` — the **canonical English statement + proof + conclusion** (`$…$`
  math + `[Prop.~B.M]` citations verbatim). This is the criterion-1 ground truth you slice.
- `Book<N>/data/diagrams/<N>.png` — the **figure**, for LABEL RESOLUTION ONLY (per HARD RULE 0): which
  point is `G`, which corners a figure-name like "HF" denotes, vertex order of a named region. Use it
  to know what the sentence's NAMES refer to — NOT as a source of geometric facts, NOT to build a
  coordinate model, NOT to audit claims. The sentence's words are the claim; the diagram only tells you
  which points the words name.
- statement-only text (proof replaced by `<prf>`): `Book/texts/<N>.txt` (Book 1, flat) /
  `Book2/data/texts/<N>.txt` (Book 2) — exists for Book 1, may be absent for Book 2. Not needed for
  the proof annotation.
- `Book2/Prop01/Main.lean` — annotation FORMAT reference only (don't imitate its monolithic proof).
- (Ignore `notes.txt`/`state.txt`/`TODO.txt`/`usellm.txt`/`WORKFLOW.md` — dev/human scratch, not ground truth.)

```
1. READ the canonical source Book<N>/data/texts_proofs/<N>.txt AND look at the diagram
   Book<N>/data/diagrams/<N>.png (the Read tool displays images). Skim Prop01 for the annotation FORMAT
   only — don't imitate its proof.

2. SLICE THE TEXT into contiguous locators "<book>.<prop>.0 ... <book>.<prop>.k":
     - .0     = euclid_intro_sentence  (enunciation + "Let ..." + "I say that ...")
     - 1..k-1 = euclid_sentence        (each a logical step)
     - last   = euclid_conclude_sentence ("Thus, ..." + QED)
   SENTENCE BOUNDARIES = EUCLID'S SENTENCES (one period-delimited sentence -> one annotation). Do NOT
   split a single Euclid sentence into two annotations, and do NOT merge two of his sentences into one.
   In particular, a trailing "For ..." / "since ..." justification clause within a sentence stays part
   of that sentence — it is Euclid explaining WHY the assertion holds, not a new claim. It gets no
   annotation of its own; its content is simply USED inside that step's proof in Phase B (it's usually
   the reason the step's claim is true). Promoting such a clause to its own euclid_sentence would
   invent structure Euclid didn't write and is LESS faithful, not more.
   (Example, Prop 2.2 sentence "And $AF$ (is) the rectangle... For it is contained by $DA$ and $AC$,
   and $AD$ (is) equal to $AB$." — ONE sentence, ONE annotation; the "For..." reason is discharged in
   its step file, not split out.)
   Each annotation text is a VERBATIM slice of the source; the slices tile the WHOLE file, joined by
   single spaces. (This is the criterion-1 contract — get it exact.)

3. WRITE THE SKELETON with PLACEHOLDER claims — do NOT design the Lean types yet:
       euclid_sentence "<loc>" "<verbatim text>" (step_n : True) := by sorry
   (True is the placeholder claim; the two structural sentences take no claim/body.) This is a
   pure text-tiling pass — the only goal is that the SENTENCES are right.

4. GATE A1 — text only: python3 scripts/check_faithful.py "Book<N>/PropNN/Main.lean"
   Must report the text-map check PASS (char-for-char). Fix slicing until it passes. (The dep check
   will fail — ignore; deps aren't wired in Phase A.) Don't move to A2 until the text tiles exactly.
```

### A2 — fill the real claim types, a FEW AT A TIME (chunk, never the whole file in one think)

Replace the `True` placeholders with real claim types **in small chunks** (per HARD RULE 2 — you pick
the chunk size, e.g. 3–6 related sentences). Within a chunk, for each `step_n`:

```
1. Write its <CLAIM TYPE>: WHAT the sentence asserts, in the statement vocabulary already in the
   prop's signature + Prop01 (|·|, ∠, Triangle.area, between, equalities). Stay in the SCOPE FENCE —
   the claim, not how to prove it (HARD RULE 1: no axiom files). Earlier steps' claims are context.
   ALSO write the discharge now: := by euclid_apply (helper_<book>_stepN <args>); euclid_finish, and
   create Book<N>/PropNN/stepN.lean with a SORRY-STUB theorem helper_<book>_stepN of that claim type
   (so Main elaborates). This wires Main fully in Phase A — there is nothing to reunite later.

2. After finishing the CHUNK, (re)build to confirm Main elaborates: scripts/safe_build.sh Book<N>.PropNN.Main
   (the only SMT here is cheap construction-precondition discharge — see below; the step PROOFs are
   sorry. A type that doesn't elaborate is a claim-vocabulary or missing-object problem — fix it now,
   before the next chunk.) Then move to the next chunk until all placeholders are real types.
```

> **Constructions (object-producing `euclid_apply … as x`) DO belong in Phase A — only step PROOFs are
> deferred.** A claim type usually names objects Euclid constructs (the square's points, a parallel
> line, an intersection point). Those objects exist only if the construction ran, so you MUST write the
> `euclid_apply (proposition_M …) as x` (or `intersection_lines …`, `line_from_points …`) in Main,
> **before the sentence that uses x**, or the skeleton won't elaborate (`x` is undefined). This is
> correct and stays — constructions are scaffolding, not proof work.
> - **Why not push them to a step file?** Objects constructed inside a `helper_*` lemma do NOT escape
>   it — later sentences in Main could never reference `x`. So object-producing applies live in Main;
>   only *fact-proving* citations (that discharge a step's claim) go in `stepN.lean`.
> - **SMT cost (the real concern):** these construction applies are NOT zero-SMT — `euclid_apply` of a
>   prop with preconditions (e.g. `proposition_46` needs `distinctPointsOnLine a b AB`) discharges them
>   via a SMALL SMT query (<1s, distinctness/incidence). Fine and expected in Phase A. The EXPENSIVE
>   SMT — proving the area/length step CLAIMS — is what `:= by sorry` (in the stub step file) skips.
> - **Rule:** in Phase A you write Main (constructions + wired euclid_apply + claim types) and
>   SORRY-STUB step files ONLY. Never prove a step claim here.

When all placeholders are real types, every `stepN.lean` stub exists, and `Main` elaborates:

```
GATE A — STOP. Report the sentence map (locator -> text -> step_n type) and WAIT for human approval.
The approved step_n types are FROZEN (see below).
```

**NO big comment block.** Do **not** write a header comment block (Prop01's was removed). If you need
scratch reasoning, leave brief `-- dev:` comments inline and **delete them in the final cleanup**. The
finished files are just imports → theorem → proof.

**The approved `step_n` types are frozen.** Phase B must not change a step's type — if one turns out
wrong, that is a Phase-A error: stop and re-do A with the human, do not silently re-type. On approval
the human snapshots the claim types: `python3 scripts/check_steps.py --save Book<N>/PropNN/Main.lean`.
From then on `python3 scripts/check_steps.py Book<N>/PropNN/Main.lean` will FLAG any changed/weakened
claim (the analog of the `check_signatures.py` statement guard). If a claim genuinely must change,
surface it to the human for re-approval; never edit it quietly.

---

## PHASE B — PROVE EACH STEP IN ITS OWN FILE (automated)

For each sentence, fill its `Book<N>/PropNN/stepN.lean` proof, via **`prove-euclid`'s methodology**.
The stub files already exist (Phase A created them) and Main already calls them.

```
1. OPEN Book<N>/PropNN/stepN.lean (created as a sorry-stub in Phase A). It has:
     - import SystemE  (+ only the Book.PropMM it cites) ; namespace Elements.Book<N> ; open Elements.Book1
     - top comment: which [Prop.~B.M] this step must cite (AWARENESS — no dep check runs in B)
     - theorem helper_<book>_stepN (objects) (setup hyps) (earlier-step conclusions)
         (cited-prop conclusions) : <the step_n type from the frozen contract>
     - set_option systemE.solverTime 30 in  (fail-fast cap)

2. PROVE IT via prove-euclid (explicit euclid_apply chains, the pattern gallery, the 30s rule).
   If a step is too big (>30s) or not entailed: SORRY-FIRST —
     a. stub helper_<book>_stepN_<sub> lemmas (own stepN_<sub>.lean files) with := by sorry,
     b. write the parent's proof assuming them and confirm the parent SKELETON elaborates,
     c. only THEN prove each sub in its own file.
   (Same "confirm skeleton before filling leaves" discipline, recursing down.)

3. (OPTIONAL) SKELETON-DISCHARGE CHECK before investing in a hard step: with the step still sorry,
   build Main and check the sentence's euclid_finish (and downstream chain) closes ASSUMING the step.
   If it doesn't close even with the step assumed true, the step's TYPE is wrong — re-examine the
   Phase-A contract; don't waste effort proving it.

4. GATE B — each step file builds with ZERO sorry:
     scripts/safe_build.sh Book<N>.PropNN.stepN
   "Build completed successfully" with a sorry warning is NOT done (see prove-euclid NEVER FAKE IT).
```

Independent steps can be proved in any order / by different agents — each owns its own `stepN.lean`.

---

## FINAL GATE — verify + clean up (NOT a phase; nothing to reunite)

`Main.lean` is ALREADY fully wired from Phase A (each `euclid_sentence` body does
`euclid_apply (helper_<book>_stepN …); euclid_finish`), and the step files now carry real proofs. So
there is no collect/move/reunite. Just verify and tidy:

```
1. GATE (quick): python3 scripts/check_faithful.py "Book<N>/PropNN/Main.lean"  — fast sanity on Main
   (text tiling + best-effort deps). This ALSO lints Main's body for forbidden bulk goal-closers
   (linarith/nlinarith/ring/simp/omega/...) — Main must close its goal through the
   euclid_sentence/euclid_apply chain only; any such tactic in Main fails the check (step files exempt).

2. GATE (AUTHORITATIVE):
     scripts/safe_build.sh Book<N>.PropNN.Main   # whole prop builds, ZERO sorry / errors
     scripts/check_faithful.sh Book<N>           # text + deps book-aware MUST PASS
   Only when this passes is the prop faithful.

3. CLEANUP. Delete ALL dev scaffolding — `-- dev:` notes, per-step TODOs, stale `set_option … 30`
   caps that are no longer load-bearing, any header comment block. Finished files are just
   imports → theorem → proof. Faithfulness lives in the euclid_sentence annotations, not in comments.
```

Reminder of how Main is structured (built in Phase A; here only for reference):
- `euclid_intros`; `euclid_intro_sentence "<book>.<prop>.0" "<intro text>"`.
- per sentence: object-producing `euclid_apply (proposition_M …) as x` BEFORE the sentence (the bound
  `x` must outlive it); then `euclid_sentence "<loc>" "<text [Prop.~B.M]>" (step_n : <claim>) := by`
  `euclid_apply (helper_<book>_stepN …)` then `euclid_finish`.
- the final chain (`rw`/`exact` of the step results) → goal; `euclid_conclude_sentence "<loc>" "<concl>"`.
- CITATION RULE (relaxed): every cited `[Prop.~B.M]` must be reachable through SOME `euclid_apply` in
  the block (a raw construction apply OR an applied `helper_` whose closure contains it). Plain
  `euclid_finish` bodies are otherwise fine. NEVER discharge a cited step with term-mode
  `:= by exact proposition_M …` (bypasses recording).

---

## INTEGRITY — the faithfulness-specific failure modes (read first)

`prove-euclid`'s NEVER FAKE IT rules all apply (no `sorry`/`admit`/`native_decide`/`axiom` in a
finished proof; "it builds" ≠ proved). On top of those:

- **Never fake criterion 2.** The text-map check only verifies texts *tile*; whether the `step_n`
  type actually means what the sentence says is HUMAN-checked. Attaching real Euclid text to a
  **vacuous or weakened** `step_n` type passes the machine and silently breaks faithfulness. The
  `step_n` type MUST genuinely capture the sentence's claim. This is the single most important rule
  unique to this skill.
- **Never change a `proposition_*` statement.** The signature is sacred and statement-faithfulness-
  checked. The signature guard (`scripts/check_signatures.py`) snapshots all statements; the human
  runs it afterward and any CHANGED/REMOVED is a red flag. If you become convinced a statement must
  change, STOP and ask the human with the specific reason — do not edit it.
- **Don't game the dep check.** Reaching a prop's number some incidental way is not the point; the
  cited prop should genuinely be the one the step's reasoning uses. (The checker is lenient by spec —
  reference, not proof-of-use — so the honesty is on you.)

## WORKING ALONGSIDE OTHER AGENTS

- One agent per proposition. You own everything in `Book<N>/PropNN/` (Main + stepN files). Do not
  touch another prop's folder.
- No git mutations (the human owns git; it's the safety net). Read-only git is fine.
- Within a prop, Phase-B step files are independent — fine to prove in parallel.

## DON'T

- Don't one-shot: never write the whole faithful proof and run it to "see if it works" (prove-euclid
  rule 0). Phase A skeleton → Phase B step files → final gate, always.
- Don't recreate a `Scratch/` dir or a `_steps.lean` merge file, and don't add a "Phase C reunite"
  step — the folder layout makes those obsolete (done props are ALREADY relocated).
- Don't change a frozen `step_n` type to make a leaf close — that's a Phase-A error; re-do A.
- Don't discharge a cited step with term-mode `exact` (the dep check won't see it).
- Don't report a prop faithful until `check_faithful.sh Book<N>` (olean) passes AND the build has
  zero `sorry`.