# 09 — "Cheapest next move" — rank candidates by how much is already in context

**Status:** idea · **Serves:** #1 (reasoning), #2 (search) · **Effort:** med · **Priority:** high (the most reasoning-relevant query)

> Builds ON [01](01-conclusion-index.md)'s DB but adds two layers: the agent's CURRENT CONTEXT + a matcher
> + cost ranking. It answers "what's my best LEGAL MOVE given THIS proof state," not just "what exists."

## Problem it solves

The DB ([01]) answers "what concludes/consumes/mentions X." But the agent's real question at a node is:
**"given the atoms I ALREADY have in context, which lemma gets me to my goal with the LEAST additional
work?"** A lemma whose 5 hyps are all already in context is a free win; one needing 3 new sub-proofs is
expensive. Today the agent can't see that ranking — it picks a lemma, then discovers mid-wire how many
hyps it can't supply.

## Why it helps (in cost terms)

Directly ranks the agent's next moves by cost, so it spends cognition on the cheapest viable path first
instead of discovering expense by failing. This is the forward+backward INTERSECTION ("reachable in one
step from my state"), the single most decision-relevant query.

## Sketch

1. **Get context:** the pipeline already produces it — `check_step --context <node>` (trace_state) lists
   the ground atoms in scope. Feed those to the query.
2. **Candidate set:** from [01], the lemmas/axioms/props whose CONCLUSION matches the goal shape (backward).
3. **Match each candidate's hyps against context — FIRST-ORDER MATCHING (the crux):**

   **Phase A — conclusion pins (always unambiguous).** The agent has already decided its claim via SF
   before it ever queries — the goal is a FULLY GROUND atom with real figure names (`¬(b.onLine EF)`,
   not a wish). Matching the lemma conclusion against that goal is deterministic: each syntactic position
   in the conclusion binds exactly one hole (`¬(x.onLine M)` → `{x→b, M→EF}`). No symmetry concern,
   no ambiguity. This is by design — SF precedes search.

   **Phase B — hyp search over remaining free variables.** After Phase A, some lemma args are bound;
   the rest are FREE (not mentioned in the conclusion). For each free variable, the search space is
   "which context atom of the right type to assign it." This is the only real search:
   - For each unbound free var, try every same-type context atom.
   - Extend ONE CONSISTENT substitution across all hyps — if hyp₁ forces `L→AB` and hyp₂ forces
     `L→CE`, reject that branch immediately.
   - Goal: find the assignment that **minimizes unsatisfied hyps** (not just "find any match") →
     needs branch-and-bound: keep running best, prune branches whose partial lower bound already
     exceeds current best.

   **Why it's cheap.** Let m = number of free variables REMAINING after Phase A, c = context size
   (~10–20 atoms). Worst case is c^m — NOT n! (factorial would be permutations; this is just
   assignment). Consistency pruning shrinks the branching factor at each depth (once `L→AB` is
   committed, every subsequent hyp with `L` checks in O(1) — no re-search). In practice m ≤ 3–4 for
   these figure lemmas, so the real search tree is tens to hundreds of nodes — sub-millisecond
   exhaustive search.

   - Count hyps that CAN'T be matched under the best consistent assignment = "still to prove."

4. **Rank ascending by (hyps-still-to-prove).** Output: candidate, the substitution, which hyps are already
   satisfied, which remain. Cheapest-to-apply first.

## Syntactic matching vs. logical equivalence — the deliberate choice

- **Pure string equality:** too weak — fails on variable renaming (lemma `x.onLine L` vs context
  `b.onLine AB`). REJECTED.
- **First-order matching (up to variable assignment):** handles renaming, deterministic, cheap, no SMT/AI.
  CHOSEN level.
- **Full logical equivalence (SMT):** too expensive, overkill.
- **The GAP and why it's SAFE:** matching misses SEMANTIC equivalence — distance symmetry `|a─b|=|b─a|`,
  `intersectsLine` orientation, packaged-vs-unfolded abbrevs (`formParallelogram`). A hyp present
  up-to-symmetry is counted "unmatched." But that only makes a candidate look MORE expensive than it is —
  it NEVER yields a false "free" match or a wrong wire. So it's a SOUND, conservative ranking heuristic; the
  cost estimate is pessimistic, which is the safe bias. (If symmetry-blindness ever hurts ranking quality
  noticeably, add a few normalization rules — canonicalize distance/angle arg order, unfold known abbrevs to
  atoms — BEFORE matching. Cheaper than SMT, closes most of the gap.)

## Open questions / risks

- **Abbrev unfolding:** `formParallelogram` in a hyp is really a conjunction of atoms; decide whether to
  match against the packaged form or the unfolded atoms (the context usually has it UNFOLDED — so unfold
  candidate hyps too, or match at the atom level).
- **Context source coupling:** depends on `--context`'s trace_state. Fine (it exists), but means this query
  runs a (cheap) build to get context, unlike the pure-parse [01] queries. Acceptable — builds are free.
- **Ranking ties:** many candidates may tie on hyp-count; secondary sort by total hyps, or by `kind`
  (prefer helper/axiom over re-deriving). Tune empirically.
