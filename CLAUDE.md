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

## Building

- `scripts/safe_build.sh Book.<Target>` — serialized `lake build` (multiple agents build at once;
  the lock prevents `.lake` corruption). Cheap helper files (`import SystemE` only) build in ~30s;
  heavy area proofs (e.g. Prop47) can take ~10 min — build those only to confirm, never to explore.
- Faithfulness check: `scripts/check_faithful.sh Book2` (needs built `.olean`).

## Committing Book work

Book targets depend on `SystemE/` (the faithfulness tactics: `Faithful.lean`, and changes to
`Solve.lean`/`Util.lean`/`Tactics.lean`) and on the `Book.lean` / `Book2.lean` aggregator import
lists. Stage those alongside `Book/` changes, or the build breaks for everyone else.
