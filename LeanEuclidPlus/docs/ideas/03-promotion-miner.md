# 03 — Promotion miner (find recurring step-shapes to lift into `Helpers/`)

**Status:** idea · **Serves:** #5 · **Effort:** low (falls out of [01](01-conclusion-index.md)) · **Priority:** 3rd

## Problem it solves

The `Helpers/` library only pays off for shapes that are actually IN it. Today we discover "this shape
recurs, it should be a lemma" by hand, ad hoc (that's how off-line/sameSide/parallel-trans got found).
We're certainly missing others — and per-step files contain LOTS of duplicates (same conclusion-shape
re-proved across props with different names).

## Why it helps (in cost terms)

Compounding: every promoted lemma converts an N-files-per-occurrence hand-build into a 1-line inline call
*everywhere it recurs, forever*. The miner tells us WHERE the library should grow to maximize that — so
library effort goes to the highest-frequency shapes, not guesses.

## Sketch

Falls out of [01]'s index almost for free. Once every declaration is indexed by `concludes` head-shape +
`hyps`:

- Group **step** rows by (normalized conclusion shape, normalized hyp-atom set) — normalizing away the
  figure-specific point/line NAMES, keeping the structural shape.
- Rank groups by **frequency across distinct props** (recurs in many props = high value) and by **how
  atomic/generic the hyps are** (all-atomic = cleanly liftable; whole-figure = not).
- Output: a ranked list of "candidate `Helpers/` lemmas" — each a shape that recurs + is generic, with the
  list of existing step files that would collapse to it.

`scripts/mine_promotions.py` (or a `find.py --promotions` mode). Run periodically, NOT in the live loop.

## Open questions / risks

- **Shape normalization** is the crux: need to canonicalize "¬(b.onLine EF) given b∈AB, AB≠EF, ¬(EF∩AB)"
  and "¬(d.onLine GH) given d∈CD, CD≠GH, ¬(GH∩CD)" to the SAME shape. This is α-renaming over points/lines
  by role. Doable but the main work.
- **False positives:** a shape can recur but have genuinely different proofs per instance — promotion only
  works if the BODY generalizes too. The miner proposes; a human/agent confirms the lemma actually proves
  generically (and the build is the final arbiter).
- Already-known instance: `Book2/Prop02/step5_hsq.lean` is a fully-generic `formParallelogram` assembly —
  a ready promotion candidate (see [07](07-generic-assembly-lemmas.md)).
