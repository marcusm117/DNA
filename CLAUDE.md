# DNA / LeanEuclidPlus

Formalizing Euclid's *Elements* in System E (LeanEuclidPlus). Proofs are checked by an SMT
backend behind `euclid_finish` / `euclid_assert` / `euclid_apply`.

## Proving / repairing Euclid proofs — READ THIS FIRST

When working on any `LeanEuclidPlus/Book*/PropNN.lean` or `HelperNN_*.lean` — proving a theorem,
filling a `sorry`, or fixing a `euclid_finish` timeout / "Could not prove" — **use the
`prove-euclid` skill** ([.claude/skills/prove-euclid/SKILL.md](.claude/skills/prove-euclid/SKILL.md)).

It encodes a decision procedure that prevents the slow "restate the goal and re-run `euclid_finish`
and hope" thrashing. The one-line summary, but read the skill for the rules and worked patterns:

> `euclid_finish` is a fast CHECKER of small explicit steps, not an oracle. **You are the prover.**
> Reason out the axiom chain by hand; isolate the failing goal into a small helper lemma; replace
> SMT search with explicit `euclid_apply`s; if a step takes >30s it's too big — decompose. Never
> run a tactic you can't justify; never build "to see"; decompose only into entailed sub-facts.

For the recurring figure-reasoning goal-shapes in Book-2 rectangle-decomposition proofs (sameSide,
point-off-a-line, line-distinctness, pasch-betweenness, `formParallelogram` assembly, `rectangle_area` /
`sum_parallelograms_area`, the parallel/angle props), the **`euclid-figures` skill**
([.claude/skills/euclid-figures/SKILL.md](.claude/skills/euclid-figures/SKILL.md)) is a reference of
goal-shape → axiom-chain recipes that `prove-euclid` consults — it gives the chain to TRY, not a lemma
to import (the facts are figure-specific; you re-prove each against your figure).

(**Prop01, Prop02, Prop03 are DONE and vetted end-to-end** — wired, zero-sorry, and passing the
authoritative olean-mode `check_faithful.sh` + `check_steps.py` + `check_signatures.py`. Use them as
references for **STRUCTURE ONLY**: what a finished `Main` looks like, the helper naming law, the
`@args` line, leaf-vs-container shape, decomposition granularity. **NEVER copy a claim TYPE or a
decomposition across props** — claims are per-sentence translations (the sentence is the claim —
`faithful-map`'s core rule), so a shape that fit Prop02's sentence is unfaithful on a prop whose sentence says
something else. Format: copy freely. Content: translate THIS prop's sentences from scratch. Every
other Book-2 prop is at a varying/in-progress state — not a reference.)

## Making proofs faithful

**Human operator guide (the simple "what do I do" loop):**
[LeanEuclidPlus/FAITHFUL.md](LeanEuclidPlus/FAITHFUL.md) — read this first if you're driving the process.

To make a proof FAITHFUL (annotate it with `euclid_sentence`s so it follows Euclid's sentence
structure — e.g. "make Book2/PropNN faithful") the pipeline is **A → gate → Assumption → B → gate → C**
(Phase A = INTERACTIVE split → map · Assumption = `scripts/assumptions.py` · Phase B = `faithful-prove`
· Phase C = mechanical):
1. **Phase A — the sentence map** (translation only, no proving). Run these two skills INTERACTIVELY, by
   hand, reviewing between them — NOT headless (headless mapping stalled; interactive one-at-a-time is the
   proven approach):
   a. **`faithful-split`** ([.claude/skills/faithful-split/SKILL.md](.claude/skills/faithful-split/SKILL.md)) —
      split the English proof text into atomic assertions → `PropNN/split.json` (TEXT-ONLY), then confirm
      it tiles the canonical text byte-for-byte: `python3 scripts/check_faithful.py --split PropNN`.
   b. **`faithful-map`** ([.claude/skills/faithful-map/SKILL.md](.claude/skills/faithful-map/SKILL.md)) —
      the ONE interactive mapper (absorbs the old translate + review). It first stamps a placeholder
      `Main.lean` from `split.json` (`python3 scripts/faithful_map_assemble.py PropNN --placeholders` →
      `(stepN : True)` + `@assumption TODO`, TEXT pulled from split.json so tiling is correct by
      construction), then FILLS each claim ONE sentence at a time (building `check_step --provable` +
      `check_faithful` as it goes), adds any structural FRAME (reductio/`by_cases`/`wlog`) or construction
      beyond the vocab (superposition → reads `Book/`+`find.py`/`SystemE`), and self-reviews.
      **Every sentence gets a REAL claim — NEVER `True`** at the end, and NEVER a restated given (that's an
      `@assumption`). Bodies stay `:= by sorry`.
   Confirm with `check_step.py PropNN --provable` (Main elaborates) + `check_faithful.py PropNN/Main.lean`
   (text tiling + construction deps + **hard-FAIL on any `True` claim**). STOPS for **human review** +
   `python3 scripts/check_steps.py --save PropNN/Main.lean`.
   (Retired: the old headless `faithful-translate` / `faithful-review` / `scaffold_translate.py` 3-agent
   split — `faithful-map` does it all interactively. The headless driver `run_faithful.py` now batches
   ONLY the two automatable phases — `assumptions` + `prove`; split/map/`--save`/Phase-C are manual.
   Monitor a batch with `scripts/monitor_tui.py`.)
2. **Assumption Phase — mechanical, the HUMAN runs a script (between the Phase-A save and Phase B):**
   `python3 scripts/assumptions.py <propdir>`. For every `-- @assumption ("text", type)` it materializes
   a `have stepK_assumptionN : type := by sorry` (every assumption gets a have, no exceptions), fires
   `euclid_finish` at a 3s cap, and persists: closes → `:= by euclid_finish` + `-- @assumption_valid`
   (a free, node-invisible fact the Phase-B agent skips); else → `:= by sorry` + `-- @assumption_gap`
   (a real node Phase B proves like any other). Writes the valid/gap tags to
   `scripts/assumption_tags.json` (agent-write-denied, like the signature baselines) and prints a gap
   report. Runs in **two fail-closed steps**: STEP A materializes the sorry haves + build-checks Main;
   FAIL (usually a `wlog … generalizing` frame — the have shifts `Hsym`'s arity) ⟹ leave the haves, stop
   (human manually adds the redundant arg to the `exact Hsym …` reduction — NEVER delete the have — then
   `--tag-only`). STEP B classifies + tags, auto after a clean STEP A. `--dry-run` reverts everything
   (diagnostic). `check_steps --save` is NOT re-run. Refuses a wired/post-Phase-B Main. Downstream `--all`
   (and `check_faithful` at gate C) HARD-enforce: every @assumption is a helper-sig binder (#1 FORCE) with
   its materialized have (#3 PARITY), and unchanged type (#2a, vs step_signatures) + valid/gap tag (#2b,
   vs assumption_tags.json).
3. **`faithful-prove`** ([.claude/skills/faithful-prove/SKILL.md](.claude/skills/faithful-prove/SKILL.md)) —
   Phase B: prove each step with the **recursive SF/SP/P atom** (delegates to `prove-euclid`). The agent
   creates/proves `stepN.lean` (recursing into `have`+backing files until every build ≤30s) and
   verifies each node with `scripts/check_step.py <propdir> <node>` (runs SF→SP→P, stops at first fail;
   this checks ONLY that node). Driving order: certify leaves, confirm each container/step with
   `--subtree <node>` (audits that node's whole cone, scoped — not the rest of the prop), bottom-up;
   `--all` is the single FINAL audit, run ONCE — NEVER mid-work to hunt a failure. `--all` also enforces
   **criterion-3 deps** (every cited `[Prop.~B.N]` satisfied by a Main construction `… as …` OR the
   sentence's helper cone); `check_step --dependency` isolates that check fast (number-only — the human's
   gate-C olean check is the book-aware authority).
   **Main's bodies stay `:= by sorry`
   throughout — the agent NEVER wires Main; the script does all wiring/`trace_state` transiently and
   reverts.** Dev-state files import NO pipeline (helper/step) files — only `SystemE` + cited
   propositions; the script adds/removes a helper import alongside its wiring (so per-node checks pull
   in only that node's olean — fast + isolated). Ends when `scripts/check_step.py <propdir> --all` exits 0.
4. **Phase C — mechanical, NOT a skill (the human runs it):**
   `python3 scripts/wire_main.py <propdir>` (commits the wiring, strips the 30s caps → 300s default,
   builds Main once — guaranteed green if `--all` passed) then `scripts/check_faithful.sh Book2` +
   `check_steps.py` + `check_signatures.py`. `wire_main.py --unwire` reverses it back to Phase B.

The certainty model: every node **suppliable** (SP — the zero-SMT `(by assumption)` wire discharges its
hyps in its container) + every **container**'s trailing tactics close from its sub-node claim types (the
SF-side build: sub-`have`s `sorry`, real tail present) + every **leaf** backing file **provable** (P —
builds isolated, zero-sorry) + **no stray sorry**, audited bottom-up by `--all`, ⟹ the final wired build
cannot fail. (A **container** backing file — one with its own `have` sub-nodes — is NOT P-built: its
trailing tactics are certified by that container build, its leaves by their P; re-building it to "prove"
it would just redundantly re-run those ≤30s queries bundled past the wall. NOTE: SP does NOT run a
container's trailing tactics — it stubs them to `sorry` and checks only hypothesis presence.)
Correctness/suppliability are mechanical (Lean); only the claim-matches-the-English check (gate A) is
human. **Caps are uniformly 30s during dev** (SMT `set_option` + a 30s wall in `check_step`); exceed
either ⟹ DECOMPOSE into more backing files, never raise a cap.

**Layout: one folder per Book-2 proposition** — `Book2/PropNN/Main.lean` (the proposition + its
`euclid_sentence`s) and `Book2/PropNN/stepN.lean` (one backing file per sentence, theorem
`helper_<book>_<prop>_stepN`; a hard step adds sub-files, same naming law `node ≡ file ≡ helper_<book>_<prop>_node`).
The pipeline is: A = sentence map in Main, all-sorry (human review) → B = prove each backing file in
the folder via `check_step.py` → C = `wire_main.py` + checks. There is NO `Scratch/` dir and NO
"reunite" step — files are written where they belong and stay.
Book 1 (`Book/Prop*.lean`) is FLAT and untouched. Book-2 props are all relocated into folders;
already-done props keep their proofs in `PropNN/Main.lean` — to make one faithful, add `stepN.lean`
files in its folder (don't recreate scratch/merge). (Prop01/02/03 are the done, vetted props — use
them as STRUCTURE references only, never to copy a claim type or decomposition; see the note above.
Every other Book-2 prop is at a varying/in-progress state — follow the skills' described shapes.)

## Tool & shell hygiene (applies to ALL work here — avoids wasted turns and permission prompts)

- **⛔ RUN EVERY COMMAND BARE FROM THE REPO ROOT — NEVER prefix with `cd …` and NEVER chain with `&&`,
  `;`, or pipes.** The session cwd is ALREADY the repo root (`…/DNA`), and git + the `scripts/…` tools
  work from anywhere in the repo, so a leading `cd` is pointless AND harmful. Permissions match the WHOLE
  command string: `git log …` matches the `Bash(git log:*)` allow rule and runs silently, but
  `cd /…/DNA && git log …` matches NEITHER `cd:*` NOR `git log:*` → it pops a permission prompt for a
  read-only command that's already allowed. Same for `cd … && python3 scripts/…`. So: just
  `git log …` / `git show …` / `python3 scripts/check_step.py …`, never wrapped. (`scripts/check_*` and
  `wire_main` also run bare — no pipes, no `timeout` wrapper; read what they print.)
- **⚠ The `Grep` and `Glob` TOOLS do NOT exist in this harness — do NOT try to call them.** Read-only
  bash inspection IS allowed here. A PreToolUse hook (`.claude/hooks/bash_hygiene.py`) governs bash:
  read-only inspection (`grep`/`rg`/`egrep`/`fgrep`/`find`/`cat`/`head`/`tail`/`ls`/`wc`) runs freely;
  only in-place transformers (`sed`/`awk`/`jq`) and ad-hoc code (`python3 -c`, heredocs) are blocked
  (use Read/Edit instead). So:
  - **read a KNOWN file → the Read tool** (a slice `sed -n '76,100p' f` is `Read(f, offset 76, limit 25)`);
    it's clickable and never prompts — prefer it for a path you already know.
  - **find files → bash `find` or `git ls-files`** · **search contents → bash `grep`/`rg`**. (There is no
    Grep/Glob tool to fall back on — use bash or Read.)
  - **find a LEMMA/AXIOM/PROP by what it concludes/consumes/mentions → `python3 scripts/find.py …`**
    (the sanctioned smart-grep over the declaration database — "what gets me `¬intersectsLine`?"
    `--concludes "¬intersectsLine"`; "what consumes a parallelogram?" `--consumes formParallelogram`;
    "what axioms define this opaque pred?" `--mentions intersectsLine --kind axiom`; also `--cites` /
    `--depends-of` / `--name` glob / `--grep` docstring). Use it INSTEAD of grepping `SystemE/Theory/…`
    or guessing signatures. It auto-rebakes; `python3 scripts/bake_index.py --rebuild` forces a full
    re-parse. The parse-only test suite is `python3 -m pytest tests/`.
  - **`python3 scripts/check_step.py …` / `check_steps.py` / `check_faithful.py` / `check_signatures.py`
    / `scripts/check_faithful.sh` / `python3 scripts/wire_main.py …` / `python3 scripts/scaffold_step.py …`
    / `python3 scripts/assumptions.py <propdir> [--tag-only|--dry-run]`** — the build/verify pipeline,
    backing-file scaffolder, and Assumption Phase. Run BARE, no pipe to `grep`/`head` (the hook denies the
    pipe; just read what the script prints). `scaffold_step.py <file-or-propdir> <node>` creates a
    skeleton backing file with correct naming law + 30s cap + claim type pre-filled — for BOTH Main
    `euclid_sentence` steps and `have` sub-nodes (Phase B uses this to avoid boilerplate; new node ⟹
    scaffold first). `assumptions.py` is the Assumption Phase, run by the agent via the
    `/faithful-assumptions` skill (all modes — the tags it writes are mechanical + build-verified, so no
    human `--save`-style gate is needed; `scripts/assumption_tags.json` stays agent-Write/Edit-denied so
    only the script writes it).
  - **read-only git**: `status`/`diff`/`log`/`show`/`branch`/`blame`/`ls-files` (git mutations are
    denied by policy — the human owns git, it's the safety net).
  - **path/shell helpers**: `cd LeanEuclidPlus` (the one allowed cd — see the bare-command rule above),
    `pwd`, `mkdir`, `realpath`/`dirname`/`basename`, `echo`, `lake env`/`lake exe faithful_export`.
  If you genuinely need something off this list, ASK the human to add it to the allowlist + hook rather
  than working around the denial.

## Building

- **The agent is HARD-DENIED raw `lake build` / `scripts/safe_build.sh`** (faithful-only repo). All
  agent builds go through the faithful scripts, which spawn `lake` internally under the build lock +
  a 30s wall: `python3 scripts/check_step.py <propdir> <node>` (Phase B per-node SF→SP→P) /
  `--provable` with NO node (Phase A: build Main, tolerate sorry) and `python3 scripts/wire_main.py
  <propdir>` (Phase C). See FAITHFUL.md for the surface.
- `scripts/safe_build.sh Book.<Target>` — serialized `lake build`, **for HUMANS** (the one-time full
  `lake build Book Book2`, ad-hoc checks). The lock prevents `.lake` corruption when many build at once.
- Faithfulness check: `scripts/check_faithful.sh Book2` (needs built `.olean`).

## Committing Book work

Book targets depend on `SystemE/` (the faithfulness tactics: `Faithful.lean`, and changes to
`Solve.lean`/`Util.lean`/`Tactics.lean`) and on the `Book.lean` / `Book2.lean` aggregator import
lists. Stage those alongside `Book/` changes, or the build breaks for everyone else.
