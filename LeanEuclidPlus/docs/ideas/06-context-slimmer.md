# 06 — Context slimmer (report which hyps a proof actually used)

**Status:** idea · **Serves:** #1, #3 · **Effort:** low-med · **Priority:** Program 3 (cleanup), opportunistic

> **NOT "just cleanup."** Two distinct payoffs: (1) it attacks the **#1 timeout cause** (bloated context —
> a steady multiplier on the whole pipeline), and (2) it **feeds [10](10-contract-deps-incremental-certs.md)'s
> `@deps`** — slimming first drops unused hyps, so the surviving binders are exactly the ones `@deps`
> attributes (fewer edges to declare, smaller dep graph). The cheap **drop-each-hyp** version below is sound
> (the build is the check — it can only report "unused" when removal still proves, so it never strips an
> essential hyp) and needs zero new infra; do that before the principled UNSAT-core version.

## Problem it solves

Bloated context is the #1 cause of `euclid_finish` timeouts (the solver searches over every hyp in scope).
`check_step --context` shows what's IN scope, but not what was NEEDED. So signatures accrete hyps the proof
never used, every one of which slows the solver and invites timeouts on the NEXT node that inherits them.

## Why it helps (in cost terms)

Smaller context ⟹ faster solver ⟹ fewer spurious timeouts ⟹ fewer re-think loops. Also helps SP: a leaner
signature has fewer hyps to supply, so fewer suppliability failures. It's a steady multiplier on the whole
pipeline, not a one-shot.

## Sketch

After a leaf proves (P green), determine which hypotheses were actually used and report the unused ones so
the agent can drop them from the signature. Options for "which were used":
- Lean's `#print axioms` / unused-variable linter is too coarse.
- A `trace`-based approach: re-run with the solver reporting its used-assumptions core (z3/cvc5 can emit an
  UNSAT CORE — the minimal hyp subset that closed the goal). The translator would need to map the core back
  to the Lean hyp names. This is the principled version.
- Cheaper heuristic: try dropping each hyp and re-proving (builds are free) — a hyp whose removal still
  proves was unused. O(#hyps) builds per leaf, but free.

Report: "`step7_dfpar_doff` proved using {hbAB, hABneEF}; UNUSED: {…} — consider slimming."

## Open questions / risks

- UNSAT-core → Lean-hyp-name mapping is real translator work (the principled path).
- The drop-each-hyp heuristic is simple and infra-light but O(#hyps) builds; fine under the free-build cost
  model, but slower wall.
- Interaction with the no-witness lemma lesson: some hyps (like `L ≠ M`) are ESSENTIAL even though a naive
  "is it used" check on a *different* proof path might miss them — don't auto-strip, just REPORT and let the
  agent decide.
