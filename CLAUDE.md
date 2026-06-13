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

Reference example of a finished, faithful proof: `LeanEuclidPlus/Book2/Prop01.lean`.

## Making proofs faithful

**Human operator guide (the simple "what do I do" loop):**
[LeanEuclidPlus/FAITHFUL.md](LeanEuclidPlus/FAITHFUL.md) — read this first if you're driving the process.

To make a proof FAITHFUL (annotate it with `euclid_sentence`s so it follows Euclid's sentence
structure — e.g. "make Book2/PropNN faithful") the pipeline is **A → gate → B → gate → C** (two
skills + one mechanical step):
1. **`faithful-map`** ([.claude/skills/faithful-map/SKILL.md](.claude/skills/faithful-map/SKILL.md)) —
   Phase A: TRANSLATE each sentence into a Lean claim type in `PropNN/Main.lean`. Bodies are **all
   `:= by sorry`; NO step files; NO `euclid_apply (helper…)` wiring** (the all-sorry Main elaborates
   cheap/SMT-free). STOPS for **human review** + `check_steps.py --save`.
2. **`faithful-prove`** ([.claude/skills/faithful-prove/SKILL.md](.claude/skills/faithful-prove/SKILL.md)) —
   Phase B: prove each step with the **recursive SF/SP/P atom** (delegates to `prove-euclid`). The agent
   creates/proves `stepN.lean` (recursing into `have`+backing files until every build ≤30s) and
   verifies each node with `scripts/check_step.py <propdir> <node>` (runs SF→SP→P, stops at first fail;
   this checks ONLY that node). Driving order: certify leaves, confirm each container/step with
   `--subtree <node>` (audits that node's whole cone, scoped — not the rest of the prop), bottom-up;
   `--all` is the single FINAL audit, run ONCE — NEVER mid-work to hunt a failure.
   **Main's bodies stay `:= by sorry`
   throughout — the agent NEVER wires Main; the script does all wiring/`trace_state` transiently and
   reverts.** Dev-state files import NO pipeline (helper/step) files — only `SystemE` + cited
   propositions; the script adds/removes a helper import alongside its wiring (so per-node checks pull
   in only that node's olean — fast + isolated). Ends when `scripts/check_step.py <propdir> --all` exits 0.
3. **Phase C — mechanical, NOT a skill (the human runs it):**
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
`helper_<book>_stepN`; a hard step adds sub-files, same naming law `node ≡ file ≡ helper_<book>_node`).
The pipeline is: A = sentence map in Main, all-sorry (human review) → B = prove each backing file in
the folder via `check_step.py` → C = `wire_main.py` + checks. There is NO `Scratch/` dir and NO
"reunite" step — files are written where they belong and stay.
Book 1 (`Book/Prop*.lean`) is FLAT and untouched. Book-2 props are all relocated into folders;
already-done props keep their proofs in `PropNN/Main.lean` — to make one faithful, add `stepN.lean`
files in its folder (don't recreate scratch/merge). Prop01 shows the OUTPUT shape (annotated by hand,
monolithic), `Book2/Prop02/` shows the real pipeline output.

## Tool & shell hygiene (applies to ALL work here — avoids wasted turns and permission prompts)

- **Read files with the Read tool; search with Grep/Glob. Never shell out to `cat`/`head`/`tail`/
  `sed`/`awk`/`find -exec` to read or slice a file** — `sed -n '76,100p' f` is just `Read(f, offset 76,
  limit 25)`, `grep -n foo Book/*.lean` is just `Grep`. These are allowed, faster, clickable, never prompt.
- **Never chain shell commands** with `;`, `&&`, or pipes in one Bash call (e.g.
  `cd …; echo …; grep …; sed …`). Permissions match the WHOLE command string, so a multi-command blob
  can't match a simple allow rule and pops a prompt even when each piece alone is fine. One lookup per
  call — and prefer Read/Grep over Bash for lookups.
- Run `check_faithful.*` **bare** (no pipes, no `timeout` wrapper). To inspect output, read what it prints.
- git mutations are denied by policy (the human owns git — it's the safety net). Read-only git is fine.

## Building

- **The agent is HARD-DENIED raw `lake build` / `scripts/safe_build.sh`** (faithful-only repo). All
  agent builds go through the faithful scripts, which spawn `lake` internally under the build lock +
  a 30s wall: `python3 scripts/check_step.py <propdir> <node>` (Phase B) / `--sufficient` (Phase A,
  build Main) and `python3 scripts/wire_main.py <propdir>` (Phase C). See FAITHFUL.md for the surface.
- `scripts/safe_build.sh Book.<Target>` — serialized `lake build`, **for HUMANS** (the one-time full
  `lake build Book Book2`, ad-hoc checks). The lock prevents `.lake` corruption when many build at once.
- Faithfulness check: `scripts/check_faithful.sh Book2` (needs built `.olean`).

## Committing Book work

Book targets depend on `SystemE/` (the faithfulness tactics: `Faithful.lean`, and changes to
`Solve.lean`/`Util.lean`/`Tactics.lean`) and on the `Book.lean` / `Book2.lean` aggregator import
lists. Stage those alongside `Book/` changes, or the build breaks for everyone else.
