# 04 — Numeric ℝ² realizer with N seeds (sound falsity detector)

**Status:** idea · **Serves:** #1, #3 · **Effort:** high · **Priority:** build only if [02](02-sm-smell-step.md) too weak

## Problem it solves

The deepest version of "should this even be true?" The proof IS the truth-check, but it's expensive. A
numeric model gives a CHEAP, sound *disproof*: realize the figure as concrete coordinates in ℝ² and
evaluate the claim by arithmetic.

## Why it helps + the soundness logic (one-directional!)

ℝ² (with the standard incidence/betweenness/congruence interpretation) is a MODEL of System E, so:

- **False in a valid ℝ² realization ⟹ definitely UNPROVABLE** (anything provable holds in every model).
  A *sound disproof.*
- **True in ℝ² ⟹ might STILL be unprovable** (true in that model but not derivable). So it can NEVER
  confirm truth — only refute. Same role as SMT `SAT`, different (cheaper, more decisive) oracle.

## N seeds — why multiple, not one (the agent's idea, and it's the right design)

A SINGLE realization lies in both directions: a generically-false claim can accidentally hold in a special
configuration (symmetric placement → accidental equality → looks true). Checking **N independent random
seeds** turns it into a proper *generic-position* test:

- False in ANY one valid seed → definitely unprovable (one counterexample suffices).
- True in ALL N seeds → strong evidence it's not generically false (still not a proof).

Cost of N≈10–20 is trivial (arithmetic, microseconds). The real work is the realizer that *generates* a
valid figure once; "do it N times with different free choices" is a tiny addition that makes the oracle
trustworthy enough to act on.

## Sketch

- Euclid's constructions are COMPUTABLE (drop perpendicular, extend, intersect = arithmetic), so executing
  the construction numerically yields concrete coordinates for the figure's points for free.
- For each of N random seeds (random choices for the free/given points), run the construction → coordinates
  → evaluate the claim's predicate (onLine = collinearity test, sameSide = sign test, between = ordering,
  ∠=∟ = dot-product zero, area = determinant) with a numeric tolerance.
- Report: "false in seed k (coords …)" → sound disproof; or "held in all N" → proceed.
- This is the SM step's stronger cousin — NOT part of SF (SF is sufficiency, not truth).

## Open questions / risks

- **Degenerate seeds:** three "random" points accidentally collinear → false negatives. MUST reject-and-
  resample degenerate configs before trusting a seed.
- **Building the realizer is the heavy lift:** generating a valid figure from the construction is itself a
  small constraint-solve (the givens constrain the frees). This is why it's last — [02]'s abstract SMT
  smell gives ~80% of the falsity-detection with ZERO new infra. Build this only if SM's `SAT` turns out to
  return `unknown` too often on false geometric claims.
- **Tolerance / floating point:** near-degenerate truths need care (is that dot-product 0 or 1e-9?). Use
  rationals or generous tolerance + resample.
- **Faithfulness:** purely a dev-time SMELL tool — it never enters a proof or the trusted kernel, so it
  can't compromise faithfulness. It only tells the agent where NOT to waste cognition.
