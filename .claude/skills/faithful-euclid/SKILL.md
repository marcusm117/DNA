---
name: faithful-euclid
description: >
  Make a LeanEuclid / System E proof FAITHFUL — annotate it so it follows Euclid's sentence
  structure and passes the faithfulness criteria (Book 1 / Book 2 of Euclid's Elements, in
  LeanEuclidPlus). Use whenever the task is "make Book2/PropNN faithful", to add
  euclid_intro_sentence / euclid_sentence / euclid_conclude_sentence annotations to a proof, or to
  re-prove a proof so each of Euclid's sentences maps to a checkable step. This skill owns the
  phase-gated, per-step-isolated pipeline; it delegates the actual proving to the `prove-euclid`
  skill. Faithfulness is NOT a refactor of the existing proof — expect to re-prove.
---

# Making Euclid proofs FAITHFUL — methodology

A proof can **compile** and still be **unfaithful**: the existing Book 2 proofs lean on
constructions and facts Euclid never had. Making a proof faithful means re-expressing it so it
follows Euclid's own sentence structure — usually **re-proving**, not refactoring. The only trusted
ground truth at this stage is the **statement** (`theorem proposition_N : ∀ … → …`); everything in
the proof body is up for grabs.

> **READ `prove-euclid` FIRST — it is a hard prerequisite.** This skill is the *faithfulness layer*:
> it owns the phases, the sentence mapping, the step-lemma conventions, and the integrity rules. All
> *actual proving* (decompose → sorry-skeleton → fill leaves, the pattern gallery, the 30s cap,
> `safe_build.sh`) is `prove-euclid`'s job and is invoked from inside Phase B here.

**On Prop01 — read it for the OUTPUT shape, not the process.**
[Book2/Prop01.lean](../../LeanEuclidPlus/Book2/Prop01.lean) was annotated **by hand, before this
pipeline existed** — it is monolithic (all `have`s inline, no step lemmas, no `Scratch/` isolation,
no phases). So use it to see *what a finished, faithful prop reads like* — the
`euclid_intro_sentence` / `euclid_sentence` / `euclid_conclude_sentence` annotations and the
locator/text/type shape (note: it has NO header comment block — the finished file is just
imports → theorem → annotated proof) — but do **NOT** copy its monolithic proving style. Your process is the
phased, per-step-isolated pipeline below; the reunited Phase-C result will resemble Prop01 in spirit
(each `euclid_sentence` discharged via an `euclid_apply` of its step), but the proofs live in
isolated `helper_<book>_step<n>` files first. Prop01 is "roughly what the end looks like," not a
template to imitate line-for-line.

---

## WHAT "FAITHFUL" MEANS (the 3 criteria)

Spec: [Book2/faithful.txt](../../LeanEuclidPlus/Book2/faithful.txt). A proof is **proof-faithful** iff:

1. **Criterion 1 — text map (machine-checked).** Every one of Euclid's sentences maps to an
   annotation; concatenating the annotation texts in locator order reproduces the canonical source
   `Book<N>/texts_proofs/<N>.txt` **character-for-character**.
2. **Criterion 2 — each step's claim (HUMAN-checked).** Each `euclid_sentence`'s Lean type genuinely
   captures what that Euclid sentence asserts. No machine checks this — which is exactly why faking
   it is the dangerous failure mode (see INTEGRITY).
3. **Criterion 3 — dependencies (machine-checked, book-aware).** Every `[Prop.~B.M]` Euclid cites is
   *referenced* (not necessarily proof-of-use) in that sentence's block.

**Statement-faithfulness** (the theorem signature matches Euclid's enunciation) is separate and
human-checked; you must NEVER change it. **Compiling** is separate again — that's `lake build`.

### How criterion 3 is actually decided (the capture model — internalize this)

A sentence's **block** = the source from the previous `euclid_sentence` up to and including this one:
the `euclid_apply` constructions before it **and** its own `:= by …` body. A citation `[Prop.~B.M]`
is satisfied iff **some `proposition_*` in the transitive dependency closure of a constant applied
(via `euclid_apply`) in that block resolves to Book B's proposition M** — matched by compiler
constant identity (book-aware), at any call depth ("function inside a function inside a function").

The one mechanical consequence: **a citation is recorded only when the prop/helper enters via
`euclid_apply`.** A construction (`euclid_apply (proposition_11'' …) as f`) is captured because it
runs as an apply; an applied step lemma (`euclid_apply (helper_2_step5 …)`) is captured and the
checker follows its closure down to the props it uses. **Term-mode `:= by exact proposition_M …`
is NOT captured** — never discharge a cited step that way.

### The two checkers

| Command | Build? | Criterion 1 | Criterion 3 | Use |
|---|---|---|---|---|
| `python3 scripts/check_faithful.py "Book<N>/Prop<NN>.lean"` | no | exact | single-file, number-only, best-effort | fast dev sanity check |
| `scripts/check_faithful.sh Book<N>` | needs built `.olean` | exact | **book-aware, transitive closure** | **authoritative final gate** |

The regex checker reads ONE file's text and cannot follow a `helper_…` into another file — so it
only meaningfully checks criterion 3 in Phase C, on the single reunited `Prop<NN>.lean`, and even
then helper-buried citations are confirmed only by the olean run. **Olean is the bulletproof
authority.** Run from `LeanEuclidPlus/`.

---

## ENVIRONMENT (same as prove-euclid — see it for detail)

- **FIRST THING: `cd` into `LeanEuclidPlus/`.** The Claude session is launched at the repo root
  (`<repo>/DNA/`, where `.claude/settings.json` lives) but ALL paths in this skill — `scripts/…`,
  `Book2/PropNN.lean`, `texts_proofs/N.txt`, `Scratch/…` — are relative to `<repo>/LeanEuclidPlus/`,
  and the permission allow-rules (`Bash(scripts/safe_build.sh:*)`, `Bash(python3 scripts/check_*.py:*)`)
  only match when the command starts with bare `scripts/…`, i.e. when run from `LeanEuclidPlus/`. So
  make your **very first Bash call** a bare `cd LeanEuclidPlus` (allowed; the Bash cwd PERSISTS across
  later calls), then run every command bare from there. Do NOT chain `cd … && …` (chained commands
  trip the prompt) — one standalone `cd` up front, then bare commands. (File READS via the Read/Grep
  tools take absolute or repo-root paths regardless, so those are unaffected — this `cd` is only so
  Bash commands resolve and match the allowlist.)
- Work from `<repo>/LeanEuclidPlus/`. `Book/` = Book 1, `Book2/` = Book 2.
- Build ONLY via `scripts/safe_build.sh <Target>` (build lock for concurrent agents). Run it **bare**
  — no `timeout`, no pipes (a piped command trips the permission prompt). z3/cvc5 are put on PATH by
  the script; you don't `source` anything.
- Per-step scratch files live under `Scratch/Book<N>/Prop<NN>/` and build in isolation via the
  `Scratch` lean_lib: `scripts/safe_build.sh Scratch.Book<N>.Prop<NN>.helper_<book>_step<n>`.
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
  use when the square must go on a chosen side. (cf. Prop47 lines 279–280 for tuple-apply usage.)
- `proposition_31 a b c BC` — line through `a` parallel to `BC` (the "draw parallel" construction).

**Common relation abbrevs** (`SystemE/Theory/Relations.lean`):
- `formParallelogram a b c d AB CD AC BD` — `a,b,c,d` corners with the named side-lines.
- `formTriangle`, `formRectilinearAngle`, `distinctPointsOnLine` — as used throughout the props.

**Imports & cross-book names (read before citing another book's prop):**
- **`import` is mandatory** to use ANY prop from another file — `euclid_apply (… proposition_M …)`
  fails unless that file is imported, even with a fully-qualified name. `import` loads the file;
  `namespace` only decides what the name is. So: `import Book.PropM` (Book 1) / `import Book2.PropM`
  (Book 2) at the top, for every prop you cite.
- **The short name collides across books.** Book 1 prop M is `Elements.Book1.proposition_M`; Book 2
  prop M is `Elements.Book2.proposition_M`. Bare `proposition_M` is ambiguous when both are in scope
  (you're in `namespace Elements.Book2` and `open Elements.Book1`).
- **Convention: fully-qualify cross-book citations.** In a Book-2 proof, write Book-1 citations as
  `Elements.Book1.proposition_M` (Book-2 ones bare, or `Elements.Book2.proposition_M`). Unambiguous,
  and it makes the book-aware faithfulness checker resolve the citation trivially. Bare names only for
  same-book references with no collision.

---

## STEP = ONE ISOLATED LEMMA FILE (non-negotiable)

The whole reason for this structure: **never wait on a giant build to discover a late step broke.**
A 100-step proof rebuilt as one unit costs an hour to find a step-100 failure. Instead:

- Each Euclid sentence is proved as its **own file** `Scratch/Book<N>/Prop<NN>/helper_<book>_step<n>.lean`,
  named `theorem helper_<book>_step<n>` (e.g. `helper_2_step5`). Builds alone in ~30s.
- **Never** name a step `proposition_*` (reserved for real Euclid props — a stray `proposition_` can
  mislead the checker) and never use a bare `stepN` theorem name.
- Sub-decompositions recurse as `helper_<book>_step<n>_<sub>` (their own files too).
- A step lemma's **hypotheses** = exactly what it needs: the objects in play, the relevant setup
  hyps, **the conclusions of earlier steps** it uses, and **the conclusion of any prop it cites**
  (passed in as a hypothesis — the lemma proves its claim *from* that, it does not re-derive the
  cited prop). Its **goal** = that sentence's `step_n` type (from the Phase-A contract). No more.
- Redundant hypotheses across step files are FINE — isolation and speed beat DRY here.

---

## PHASE DETECTION

Invoked with a path (`/faithful-euclid Book2/Prop02.lean`). Detect where you are from the file:

- **No `euclid_*` annotations in the prop** → start at **Phase A**.
- **Annotations present, but step lemmas missing / not all building** → **Phase B**.
- **All step lemmas build + main is reunited** → **Phase C** (verify + clean up).

For a future book whose sentences already exist (Books 3/4), you may be handed a prop already past
Phase A — detect and resume at B.

---

## PHASE A — SENTENCE MAP (then STOP for human review)

Goal: pin down, for every Euclid sentence, its locator, verbatim text, and the **Lean type of its
claim** — and prove the *skeleton* type-checks. No real proving yet.

> **SCOPE FENCE — READ BEFORE YOU START.** Phase A produces only the sentence *claims* (the `step_n`
> types) — WHAT each sentence asserts, not HOW to prove it. **Do NOT research proof strategy here:**
> no grepping area axioms, no checking `Triangle.area` permutation/symmetry, no studying how another
> prop discharged a step, no reading axiom signatures to plan tactics. ALL of that is **Phase B**,
> done later, per-step, in isolated files. If you catch yourself opening
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

> **WIPE THE OLD PROOF FIRST (mandatory).** The prop already compiles with an UNFAITHFUL proof. Before
> anything else, **delete the entire existing proof body** — everything AFTER `:= by` down to just
> `euclid_intros` — and build the faithful proof FRESH from the sentence skeleton. Do NOT keep the old
> tactics around and try to make them faithful, and do NOT reuse leftover `have`s / constructions.
> **Do NOT touch the signature** (`theorem proposition_N : ∀ … → … :=`): leave those lines exactly as
> they are — don't edit, reformat, or even retype them. The signature is ground truth and is checked
> independently (`scripts/check_signatures.py`); any change to it is a hard failure. You edit ONLY the
> proof body.
>
> **NEVER "just close the goal."** A faithful proof is built ONLY from the per-sentence
> `euclid_sentence` steps and their `euclid_apply`s. You may NOT discharge the proposition's goal (or
> any step) with a leftover bulk tactic — **no `linarith`/`nlinarith`/`ring`/`simp`/`omega`/big
> `euclid_finish` over the whole goal** carried over from the old proof. If a build is green but the
> goal was closed by anything other than the faithful step chain, that is a FAITHFULNESS FAILURE, not
> a success. (Pure length/area *algebra* may still go in a clearly-scoped `helper_*` lemma in Phase B —
> but that helper realizes a specific sentence's claim; it is never a catch-all goal-closer in main.)

**Per-proposition resources** (keyed by the prop NUMBER `<N>`, relative to `LeanEuclidPlus/`):
- `Book<N>/texts_proofs/<N>.txt` — the **canonical English statement + proof + conclusion** (`$…$`
  math + `[Prop.~B.M]` citations verbatim). This is the criterion-1 ground truth you slice.
- `Book<N>/diagrams/<N>.png` — the **figure**. READ IT (the Read tool shows images): it disambiguates
  the labelling (which points form the square, where `F`/`H` sit, vertex order) and makes the claim
  types much easier to write correctly.
- `Book<N>/texts/<N>.txt` — statement-only text (proof replaced by `<prf>`); exists for Book 1, may be
  absent for Book 2. Not needed for the proof annotation.
- `Book2/Prop01.lean` — annotation FORMAT reference only (don't imitate its monolithic proof).
- (Ignore `notes.txt`/`state.txt`/`TODO.txt`/`usellm.txt`/`WORKFLOW.md` — dev/human scratch, not ground truth.)

```
1. READ the canonical source Book<N>/texts_proofs/<N>.txt AND look at the diagram
   Book<N>/diagrams/<N>.png (the Read tool displays images — it disambiguates the labelling and makes
   the claim types easier to write). Skim Prop01 for the annotation FORMAT only — don't imitate its proof.

2. SLICE THE TEXT into contiguous locators "<book>.<prop>.0 … <book>.<prop>.k":
     - `.0`   = euclid_intro_sentence  (enunciation + "Let …" + "I say that …")
     - 1..k-1 = euclid_sentence        (each a logical step)
     - last   = euclid_conclude_sentence ("Thus, …" + QED)
   SENTENCE BOUNDARIES = EUCLID'S SENTENCES (one period-delimited sentence → one annotation). Do NOT
   split a single Euclid sentence into two annotations, and do NOT merge two of his sentences into one.
   In particular, a trailing **"For …" / "since …" justification clause within a sentence stays part of
   that sentence** — it is Euclid explaining WHY the assertion holds, not a new claim. It gets no
   annotation of its own; its content is simply USED inside that step's proof in Phase B (it's usually
   the reason the step's claim is true). Promoting such a clause to its own `euclid_sentence` would
   invent structure Euclid didn't write and is LESS faithful, not more.
   (Example, Prop 2.2 sentence "And $AF$ (is) the rectangle… For it is contained by $DA$ and $AC$, and
   $AD$ (is) equal to $AB$." — ONE sentence, ONE annotation; the "For…" reason is discharged in its
   helper, not split out.)
   Each annotation text is a VERBATIM slice of the source; the slices tile the WHOLE file, joined by
   single spaces. (This is the criterion-1 contract — get it exact.)

3. WRITE THE SKELETON with PLACEHOLDER claims — do NOT design the Lean types yet:
       euclid_sentence "<loc>" "<verbatim text>" (step_n : True) := by sorry
   (`True` is the placeholder claim; the two structural sentences take no claim/body.) This is a
   pure text-tiling pass — the only goal is that the SENTENCES are right.

4. GATE A1 — criterion 1 only: python3 scripts/check_faithful.py "Book<N>/Prop<NN>.lean"
   Must report criterion 1 PASS (char-for-char). Fix slicing until it passes. (Criterion 3 will
   fail — ignore; deps aren't wired in Phase A.) Don't move to A2 until the text tiles exactly.
```

### A2 — fill the real claim type, ONE sentence at a time

Now replace each `True` placeholder with the sentence's actual Lean claim — **one sentence per step,
in order**, exactly like the proof phase does leaves one at a time (don't design all types in one
giant think). For each `step_n`:

```
1. Write its <CLAIM TYPE>: WHAT the sentence asserts, in the statement vocabulary already in the
   prop's signature + Prop01 (`|·|`, `∠`, `Triangle.area`, `between`, equalities). Stay in the SCOPE
   FENCE — the claim, not how to prove it. Earlier steps' claims are available as context for later
   ones. Leave the body `:= by sorry`.

2. (Re)build to confirm THIS step's type elaborates: scripts/safe_build.sh Book<N>.Prop<NN>
   (the only SMT here is cheap construction-precondition discharge — see below; the step PROOFs are
   sorry. A type that doesn't elaborate is a claim-vocabulary or missing-object problem — fix it now.)
```

> **Constructions (object-producing `euclid_apply … as x`) DO belong in Phase A — only step PROOFs are
> deferred.** A claim type usually names objects Euclid constructs (the square's points, a parallel
> line, an intersection point). Those objects exist only if the construction ran, so you MUST write the
> `euclid_apply (proposition_M …) as x` (or `intersection_lines …`, `line_from_points …`) in main,
> **before the sentence that uses x**, or the skeleton won't elaborate (`x` is undefined). This is
> correct and stays through Phase C — constructions are scaffolding, not proof work.
> - **Why not push them to a Phase-B helper?** Objects constructed inside a `helper_*` lemma do NOT
>   escape it — later sentences in main could never reference `x`. So object-producing applies live in
>   main; only *fact-proving* citations (that discharge a step's claim) go to Phase-B helpers.
> - **SMT cost (the real concern):** these construction applies are NOT zero-SMT — `euclid_apply` of a
>   prop with preconditions (e.g. `proposition_46` needs `distinctPointsOnLine a b AB`) discharges them
>   via a SMALL SMT query (<1s, distinctness/incidence). That's fine and expected in Phase A. The
>   EXPENSIVE SMT — proving the area/length step CLAIMS — is exactly what `:= by sorry` skips. So Phase
>   A runs only cheap construction-precondition SMT, never big goal-proving SMT.
> - **Rule:** in Phase A you write constructions + `sorry` step bodies ONLY. Never prove a step claim here.

When all placeholders are real types and the full skeleton elaborates:

```
GATE A — STOP. Report the sentence map (locator → text → step_n type) and WAIT for human approval.
The approved step_n types are FROZEN (see below).
```

**NO big comment block.** Do **not** write a giant STAGE-A header comment (Prop01's was removed). If
you need scratch reasoning while working, leave brief `-- dev:` comments inline and **delete them in
the Phase-C cleanup**. The finished file is just imports → theorem → annotated proof.

**The approved `step_n` types are frozen.** Phases B and C must not change a step's type — if one
turns out wrong, that is a Phase-A error: stop and re-do A with the human, do not silently re-type.
On approval the human snapshots the claim types: `python3 scripts/check_steps.py --save Book<N>/Prop<NN>.lean`.
From then on `python3 scripts/check_steps.py Book<N>/Prop<NN>.lean` will FLAG any changed/weakened
claim (a guard against silently weakening a step to make proving easier — the analog of the
`check_signatures.py` statement guard). If a claim genuinely must change, surface it to the human for
re-approval; never edit it quietly.

---

## PHASE B — PROVE EACH STEP IN ISOLATION (automated)

For each `euclid_sentence`, in its own file, drive the proof via **`prove-euclid`'s methodology**.

```
1. CREATE Scratch/Book<N>/Prop<NN>/helper_<book>_step<n>.lean
     - import SystemE  (+ only the Book.PropMM it cites)
     - top comment: which [Prop.~B.M] this step must cite (AWARENESS — no dep check runs in B)
     - theorem helper_<book>_step<n> (objects) (setup hyps) (earlier-step conclusions)
         (cited-prop conclusions) : <the step_n type from the frozen contract> := by …
     - set_option systemE.solverTime 30 in  (fail-fast cap)

2. PROVE IT via prove-euclid (explicit euclid_apply chains, the pattern gallery, the 30s rule).
   If a step is too big (>30s) or not entailed: SORRY-FIRST —
     a. stub helper_<book>_step<n>_<sub> lemmas with := by sorry,
     b. write the parent's proof assuming them and confirm the parent SKELETON elaborates,
     c. only THEN prove each sub in its own file.
   (Same "confirm skeleton before filling leaves" discipline, recursing down.)

3. (OPTIONAL) SKELETON-DISCHARGE CHECK before investing in a hard step: in the main prop, apply the
   construction / step but stub its proof with `sorry`, and check the sentence's euclid_finish (and
   the downstream chain) closes ASSUMING the step. If it doesn't close even with the step assumed
   true, the step's TYPE is wrong — re-examine the Phase-A contract; don't waste effort proving it.

4. GATE 2 — each step file builds with ZERO sorry:
     scripts/safe_build.sh Scratch.Book<N>.Prop<NN>.helper_<book>_step<n>
   "Build completed successfully" with a `sorry` warning is NOT done (see prove-euclid NEVER FAKE IT).
```

Independent steps can be proved in any order / by different agents — each owns its own file.

---

## PHASE C — REUNITE + AUTHORITATIVE CHECK + CLEANUP (automated)

```
1. COLLECT the finished step lemmas into Book<N>/Prop<NN>_steps.lean (namespace Elements.Book<N>);
   `import Book<N>.Prop<NN>_steps` from Prop<NN>.lean. (They leave Scratch/ — a staging area.)

2. WIRE the main proof. After `euclid_intros`:
     - euclid_intro_sentence "<book>.<prop>.0" "<intro text>"
     - per sentence:
         * object-producing constructions go BEFORE the sentence (the bound object must outlive it):
             euclid_apply (proposition_M …) as x        -- or a construction axiom
         * the sentence's own claim goes INSIDE the body, brought in via euclid_apply:
             euclid_sentence "<loc>" "<verbatim text> [Prop.~B.M]"
                 (step_n : <claim>) := by
               euclid_apply (helper_<book>_step<n> <args>)   -- records the dep for criterion 3
               euclid_finish                                 -- lifts the claim onto the goal; instant
     - the final chain (rw/exact of the step results) → the goal
     - euclid_conclude_sentence "<loc>" "<conclusion text>"
   (Construction-only sentences and the two structural sentences carry no helper.)

   CITATION RULE (relaxed): the only hard requirement is that every cited [Prop.~B.M] is reachable
   through SOME euclid_apply in the block — a raw construction apply OR an applied helper whose
   closure contains it. Otherwise plain euclid_finish bodies are fine. NEVER prove a cited step with
   term-mode `:= by exact proposition_M …` (bypasses recording).

3. GATE 3a (quick): python3 scripts/check_faithful.py "Book<N>/Prop<NN>.lean"  — on the single
   reunited file (fast sanity). This ALSO lints the main body for forbidden bulk goal-closers
   (`linarith`/`nlinarith`/`ring`/`simp`/`omega`/…) — main must close its goal through the
   euclid_sentence/euclid_apply chain only; any such tactic in main fails the check (helpers exempt).

4. GATE 3b (AUTHORITATIVE):
     scripts/safe_build.sh Book<N>          # whole prop builds, ZERO sorry / errors
     scripts/check_faithful.sh Book<N>      # criteria 1 + 3 book-aware MUST PASS
   Only when 3b passes is the prop faithful.

5. COMMENT-CLEANUP PASS. Delete ALL dev scaffolding — `-- dev:` notes, per-step TODOs, reference-
   proof comments, stale `set_option … 30` caps that are no longer load-bearing, and any header
   comment block. The finished file is just imports → theorem → annotated proof (like Prop01 now).
   The faithfulness lives in the `euclid_sentence` annotations themselves, not in prose comments.
```

---

## INTEGRITY — the faithfulness-specific failure modes (read first)

`prove-euclid`'s NEVER FAKE IT rules all apply (no `sorry`/`admit`/`native_decide`/`axiom` in a
finished proof; "it builds" ≠ proved). On top of those:

- **Never fake criterion 2.** Criterion 1 only checks that texts *tile*; criterion 2 (does the `have`
  type actually mean what the sentence says?) is HUMAN-checked. Attaching real Euclid text to a
  **vacuous or weakened** `step_n` type passes the machine and silently breaks faithfulness. The
  `step_n` type MUST genuinely capture the sentence's claim. This is the single most important rule
  unique to this skill.
- **Never change a `proposition_*` statement.** The signature is sacred and statement-faithfulness-
  checked. A signature guard (`scripts/check_signatures.py`) snapshots all statements; the human runs
  `python3 scripts/check_signatures.py` afterward and any CHANGED/REMOVED is a red flag. If you
  become convinced a statement must change, STOP and ask the human with the specific reason — do not
  edit it.
- **Don't game criterion 3.** Reaching a prop's number some incidental way is not the point; the
  cited prop should genuinely be the one the step's reasoning uses. (The checker is lenient by spec —
  reference, not proof-of-use — so the honesty is on you.)

## WORKING ALONGSIDE OTHER AGENTS

- One agent per proposition. You own `Book<N>/Prop<NN>.lean`, `Book<N>/Prop<NN>_steps.lean`, and
  `Scratch/Book<N>/Prop<NN>/`. Do not touch another prop's files or another agent's scratch.
- No git mutations (the human owns git; it's the safety net). Read-only git is fine.
- Within a prop, Phase-B step files are independent — fine to prove in parallel.

## DON'T

- Don't one-shot: never write the whole faithful proof and run it to "see if it works" (prove-euclid
  rule 0). Phase A skeleton → Phase B leaves → Phase C reunite, always.
- Don't change a frozen `step_n` type to make a leaf close — that's a Phase-A error; re-do A.
- Don't discharge a cited step with term-mode `exact` (criterion 3 won't see it).
- Don't report a prop faithful until `check_faithful.sh Book<N>` (olean) passes criteria 1 + 3 AND
  the build has zero `sorry`.
