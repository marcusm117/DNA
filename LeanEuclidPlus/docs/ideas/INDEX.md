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

---

## The three programs (how these ideas actually group)

The 11 ideas are not 11 independent things — they collapse into **three programs**, ranked by what
actually helps the current goal (**finish Book 2 proofs ASAP**). Build top-down.

### Program 1 — REUSE: Helper library + Database/search  ⟵ TOP PRIORITY

"Expand the `Helpers/` library like a mini-mathlib for System-E geometry, and make it (plus every
axiom/prop) findable." Two cooperating halves — separately buildable, symbiotic:

- **The library (write lemmas):** [07](07-generic-assembly-lemmas.md) `mk_parallelogram`/`mk_triangle` +
  siblings, and whatever [03](03-promotion-miner.md)'s miner surfaces as recurring. Serves cost-source #5.
  **This is the fastest ASAP win** — a promoted lemma collapses an N-file hand-build to a 1-liner on the
  *very next* prop. Start by hand (07); defer the miner (03) until enough props are done that cross-prop
  duplication is real.
- **The database/search (find + grow lemmas):** [01](01-conclusion-index.md) `bake_index` + `find.py` —
  a parse-only, multi-axis query tool over EVERY declaration (axioms, props, helpers, steps). **`find.py`
  IS the sanctioned smart-grep** (the answer to "should we re-allow grep?" — no; give the agent this
  instead). [09 — "cheapest next move"](01-conclusion-index.md#09--cheapest-next-move-merged) is its
  flagship query (merged into 01: it's a query MODE of the same DB, not a separate idea). The DB *indexes*
  the library (reuse #5) and its miner *grows* it (03). Medium effort — it's tooling that competes with
  proving time, so build it only once axiom-search thrash is actually your bottleneck.

| # | Idea | Serves | Status | Effort |
|---|------|--------|--------|--------|
| [01+09](01-conclusion-index.md) | Fact DB + multi-axis query tool (`bake_index` + `find`), incl. "cheapest next move" ranking | #1,#2,#5 | idea | med |
| [07](07-generic-assembly-lemmas.md) | Promote generic figure-assembly lemmas (`mk_parallelogram` etc.) — **do by hand first** | #5 | partially fixed in skill | low |
| [03](03-promotion-miner.md) | Promotion miner — find recurring step-shapes to lift into `Helpers/` (falls out of 01) | #5 | idea | low |

### Program 2 — ORPHAN CHECK  ⟵ QUICK WIN, do early

| # | Idea | Serves | Status | Effort |
|---|------|--------|--------|--------|
| [11](11-orphan-reachability.md) | Orphan / reachability check — mark-and-sweep from Main; flag dead leftover files | #3,#4 | idea | low |

~15 lines reusing existing `_bottom_up`/`_containment`. Kills the recurring "dead leftover decomposition
silently passes `--check`, then blows up `--all`" thrash (the real boffDG bug). Cheap insurance while
churning decompositions — independent of everything, do it whenever.

### Program 3 — CLEANUP / DEPS / FEASIBILITY  ⟵ LATER (post-Book-2, maintenance regime)

These pay off when proofs are *done and churning* (certify-once, invalidation, readability), NOT in the
get-it-green regime. Record richly; don't build now.

| # | Idea | Serves | Status | Effort |
|---|------|--------|--------|--------|
| [10](10-contract-deps-incremental-certs.md) | Explicit named deps (`@deps`) + contract-hash certs + auto-named interface facts | #3,#4 | developing | med-high |
| [06](06-context-slimmer.md) | Context slimmer — report which hyps a proof actually used (feeds 10's `@deps`) | #1,#3 | idea | low-med |
| [02](02-sm-smell-step.md) | `SM` smell step — front-load the "don't over-decompose, `euclid_finish` closes it" check | #1,#3 | idea | low |
| [04](04-numeric-realizer.md) | Numeric ℝ² realizer with N seeds — sound falsity detector (build only if 02 too weak) | #1,#3 | idea | high |
| [05](05-timeout-diagnostics.md) | SP failure message: list only unmet binders (timeout tiers RETIRED by the 45s>30s design) | #3 | idea | very low |

### Rejected

| # | Idea | Serves | Status | Effort |
|---|------|--------|--------|--------|
| [08](08-rejected.md) | Rejected ideas + WHY (aesop for #1, review-agent for #4, thrash-counter, live-rebake) | — | decided | — |

---

## Build order (highest ROI for "finish Book 2 ASAP" first)

1. **Program 1, library half — 07 by hand** (`mk_parallelogram` + siblings). Helps the next prop directly.
2. **Program 2 — 11 orphan check.** Nearly free; kills a real thrash source; do it whenever.
3. **Program 1, DB half — 01+09**, IF axiom/lemma-search is your bottleneck. Then 03 (miner) falls out of it.
4. **Program 3 — everything else, deferred to the maintenance regime:**
   - 02 SM smell (the UNSAT-fast "don't over-decompose" cost win) — cheap, do opportunistically.
   - 06 context slimmer (also feeds 10's `@deps`).
   - 10 deps + certs + auto-naming — the readability/certify-once substrate; spike the named-wire on one
     node FIRST. The auto-named-interface-facts variant is a nice cleanup, explicitly NOT a priority.
   - 05 SP-message stripping (very low effort polish).
   - 04 numeric realizer — heavy; build ONLY if 02's abstract-SMT smell proves too weak.
