# Pipeline cost-reduction ideas — index

**Goal of this folder: DON'T FORGET.** Every good idea for reducing the cost of the faithful-proof
pipeline gets written here with *what it is*, *why it helps*, and *its open questions* — so we can
implement opportunistically (highest-ROI first) without re-deriving or losing anything. Not everything
here will be built; the captured reasoning is the deliverable.

## The cost model (the lens for ranking everything)

> **Cost = AGENT THINKING TOKENS. Builds are effectively free** (no tokens; wall time doesn't consume
> human or agent attention as long as it's not blocking either). The expensive failure mode is the
> COGNITION loop: *agent thinks it has a solution → builds → fails → re-thinks → fails → …*, multiplied
> across many nodes. So the goal is NOT "prevent failed builds" — it's **shorten each thinking burst, and
> kill wrong-path thinking before the agent invests a whole subtree of cognition in it.**

This reframes the classic intuition: a failed build is cheap; a *failed line of reasoning that spawned a
decomposition* is expensive. Front-load truth/feasibility checks to the TOP of the thinking tree.

## The five named cost sources (agent's words)

1. **Reasoning in English** — "to prove these are parallel, the argument goes this then this…"
2. **Searching for the right axiom / lemma** to apply.
3. **Testing if it works + pinpointing the failure.**
4. **Meta: are we off-track? should this work? going in circles?**
5. **Can we reuse old work?** (partially solved by the `Helpers/` library.)

## Ideas, ranked by (token-saving ÷ effort)

| # | Idea | Serves | Status | Effort |
|---|------|--------|--------|--------|
| [01](01-conclusion-index.md) | Fact DB + multi-axis query tool (`bake_index` + `find`): concludes / consumes / mentions | #1,#2,#5 | idea | med |
| [02](02-sm-smell-step.md) | `SM` smell step — short-timeout triviality/falsity check before SF | #1,#3,#4 | idea | low |
| [03](03-promotion-miner.md) | Promotion miner — find recurring step-shapes to lift into `Helpers/` | #5 | idea | low (falls out of 01) |
| [04](04-numeric-realizer.md) | Numeric ℝ² realizer with N seeds — sound falsity detector | #1,#3 | idea | high |
| [05](05-timeout-diagnostics.md) | Timeout diagnostics — last-profiler-line + context-size on wall-kill | #3 | idea | low (spike first) |
| [06](06-context-slimmer.md) | Context slimmer — report which hyps a proof actually used | #1,#3 | idea | low-med |
| [07](07-generic-assembly-lemmas.md) | Promote generic figure-assembly lemmas (`mk_parallelogram` etc.) | #5 | partially fixed in skill | low |
| [09](09-next-move-ranking.md) | "Cheapest next move" — rank candidates by hyps already in context (first-order matching) | #1,#2 | idea | med |
| [10](10-contract-deps-incremental-certs.md) | Explicit named deps (`@deps`) + contract-hash certs — "certify once, never re-audit" | #3,#4 | developing | med-high |
| [08](08-rejected.md) | Rejected ideas + WHY (aesop for #1, review-agent for #4, thrash-counter, live-rebake) | — | decided | — |

## Recommended build order (highest ROI first)

1. **01 fact DB + query tool** — the keystone: serves search (#2), reuse (#5), AND the reasoning (#1) by
   turning open derivation into menu-picking, FORWARD (what consumes what I have) and BACKWARD (what
   concludes what I want), plus attribute browse (e.g. an opaque def = the axioms that mention it).
   **03 promotion-miner falls out of it.**
2. **02 SM smell step** — cheap, front-loads truth/triviality (the UNSAT-fast "don't decompose" branch is
   an under-used cost win today).
3. **07 generic assembly lemmas** — small, surfaced by 01's miner; skill text already corrected.
4. **05 timeout diagnostics** — cheap IF the profiler-streaming spike works.
5. **04 numeric realizer** — the heavy one; build ONLY if 02's abstract-SMT smell proves too weak.
6. **06 context slimmer** — opportunistic; also feeds 10 (slim hyps ⟹ smaller dep graph to declare).
7. **10 explicit deps + contract certs** — staged; spike the named-wire on one node FIRST (de-risks the
   wired-body/regex surface) before the manifest work. Closes the `--subtree`-on-a-leaf false-confidence
   hole and turns certification into proof-churn-immune incremental caching.
