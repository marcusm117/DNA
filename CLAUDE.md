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
structure and passes the faithfulness criteria — e.g. "make Book2/PropNN faithful") use the
**`faithful-euclid` skill** ([.claude/skills/faithful-euclid/SKILL.md](.claude/skills/faithful-euclid/SKILL.md)).
It owns the phase-gated, per-step-isolated pipeline (A: sentence map → human review → B: prove each
sentence in its own `Scratch/` file → C: reunite + `check_faithful.sh` gate) and delegates the actual
proving to `prove-euclid`. Note: Prop01 was annotated by hand pre-pipeline, so it shows the OUTPUT
shape, not the process.

## Tool & shell hygiene (applies to ALL work here — avoids wasted turns and permission prompts)

- **Read files with the Read tool; search with Grep/Glob. Never shell out to `cat`/`head`/`tail`/
  `sed`/`awk`/`find -exec` to read or slice a file** — `sed -n '76,100p' f` is just `Read(f, offset 76,
  limit 25)`, `grep -n foo Book/*.lean` is just `Grep`. These are allowed, faster, clickable, never prompt.
- **Never chain shell commands** with `;`, `&&`, or pipes in one Bash call (e.g.
  `cd …; echo …; grep …; sed …`). Permissions match the WHOLE command string, so a multi-command blob
  can't match a simple allow rule and pops a prompt even when each piece alone is fine. One lookup per
  call — and prefer Read/Grep over Bash for lookups.
- Run `safe_build.sh` / `check_faithful.*` **bare** (no pipes, no `timeout` wrapper). To inspect their
  output, just read what they print.
- git mutations are denied by policy (the human owns git — it's the safety net). Read-only git is fine.

## Building

- `scripts/safe_build.sh Book.<Target>` — serialized `lake build` (multiple agents build at once;
  the lock prevents `.lake` corruption). Cheap helper files (`import SystemE` only) build in ~30s;
  heavy area proofs (e.g. Prop47) can take ~10 min — build those only to confirm, never to explore.
- Faithfulness check: `scripts/check_faithful.sh Book2` (needs built `.olean`).

## Committing Book work

Book targets depend on `SystemE/` (the faithfulness tactics: `Faithful.lean`, and changes to
`Solve.lean`/`Util.lean`/`Tactics.lean`) and on the `Book.lean` / `Book2.lean` aggregator import
lists. Stage those alongside `Book/` changes, or the build breaks for everyone else.
