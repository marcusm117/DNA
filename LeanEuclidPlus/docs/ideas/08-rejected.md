# 08 — Rejected / shelved ideas (and WHY)

Keeping these so we don't relitigate them. "Why we said no" is as valuable as the yeses.

## aesop (or another tactic engine) to automate #1 reasoning — REJECTED

- **Idea:** use aesop / a generic automation tactic to find proofs so the agent reasons less.
- **Why no:** In System E, `euclid_finish` ALREADY IS the automation — it calls z3/cvc5 over the
  translated geometric theory. aesop is a SEPARATE, non-SMT engine with NO System-E rule set; using it
  means building a second automation from scratch with none of the geometry baked in. Low ROI.
- **What serves #1 instead:** [01 conclusion-index](01-conclusion-index.md) — backward-chaining the
  reasoning into menu-picks does far more for #1 than a second prover would.

## A review/meta agent for #4 ("are we off-track / going in circles?") — SHELVED

- **Idea:** a smarter reviewer agent that watches the proof attempt and judges strategy.
- **Why shelved:** Needs flexible judgment (hard to script well), and empirically the proofs DO come out —
  the model is already decent at #4. High effort, unclear ROI. Revisit only if thrash data shows a
  systematic strategic-blindness pattern a heuristic can't catch.

## Thrash counter (warn after N rebuilds of the same node) — REJECTED (agent's call)

- **Idea:** `check_step` counts attempts per node, warns at the 4th rebuild ("you're looping, rethink").
- **Why no:** The agent often LEARNS something on each attempt (narrowing the failure), so a blunt
  attempt-count punishes legitimate progress and gives a false "you're stuck" signal. Risky, low precision.
  The truth/feasibility front-loading ([02], [04]) attacks the SAME thrash at its ROOT (don't start the
  doomed path) without the false positives.

## Live re-bake of the index on every search (full re-parse each call) — REPLACED

- **Idea:** rebuild the whole index every time the agent queries.
- **Why no, and what replaced it:** Pointless — parsing is already instant, so a full re-parse per query
  buys nothing. REPLACED by INCREMENTAL auto-bake (re-parse only mtime/hash-changed files per query) +
  a manual `--bake`/`--rebuild` for first-run / massive-change. See [01](01-conclusion-index.md).

## Speeding up builds / the build lock — NOT PURSUED

- **Idea:** parallelize or speed the 30s-walled serialized builds.
- **Why no:** Per the cost model, wall time costs neither tokens nor (blocking) human attention. The fix
  for "too many slow builds" is FEWER builds (kill wrong-path cognition via [01]/[02]), not faster ones.
  Infra-heavy, wrong target.
