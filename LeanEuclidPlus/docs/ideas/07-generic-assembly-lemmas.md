# 07 — Promote generic figure-assembly lemmas (`mk_parallelogram`, …)

**Status:** skill text CORRECTED; lemmas not yet added · **Serves:** #5 · **Effort:** low · **Priority:** 3rd-ish

## Problem it solves

`euclid-figures` Family 5 used to claim "NO library lemma for figure assembly — it threads the whole
figure." **That was wrong** — and an agent reading it would needlessly hand-build every `formParallelogram`.
`Book2/Prop02/step5_hsq.lean` proves it: its `formParallelogram d e a b DE AB AD BE` is universally
quantified over the points/lines, and EVERY hypothesis is atomic (incidences, `e≠b`, one `sameSide`, two
`¬intersects`). So assembly IS genericizable into a `Helpers/` lemma.

(Skill corrected on 2026-06-18 — Family 5 now says "LIBRARY-ABLE" with the caveats below.)

## Why it helps (in cost terms) — but a SMALLER win, hence not #1

A `mk_parallelogram` lemma collapses each assembly leaf to one call. BUT two honest caveats make it
lower-priority than off-line/sameSide:
1. The hard hypothesis is still the `sameSide` — you derive THAT via `Helpers/SameSide.lean` regardless,
   and once you have it the inline `exact ⟨…, ss, …⟩` constructor (as `step7_dfpar` does) is ALREADY cheap.
   So the marginal saving over "derive sameSide + inline-assemble" is modest.
2. `formParallelogram` has vertex-ordering / orientation variants → needs a few siblings (like off-line did).

## Sketch

- Add `Helpers/Parallelogram.lean` with `mk_parallelogram` (the `step5_hsq` shape) + sibling orientations
  as they recur. Namespace `Elements`, atomic hyps only (so `(by assumption)` discharges them).
- Let [03 promotion miner](03-promotion-miner.md) surface WHICH vertex-orderings actually recur, rather than
  guessing all of them up front.
- `formTriangle` is the same story (three pairwise-distinct lines + incidences) — a `mk_triangle` sibling.

## Open questions / risks

- How many ordering variants are really needed? Don't pre-build all permutations — let the miner / actual
  call sites drive it (same discipline as the off-line siblings).
- Watch the same soundness trap as the no-witness off-line lemmas: include EXACTLY the atomic hyps the
  construction needs (a missing distinctness → `SAT`/unprovable). The build is the check.
