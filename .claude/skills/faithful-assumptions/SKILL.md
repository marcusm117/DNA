---
name: faithful-assumptions
description: >
  REPAIR a Euclid prop (LeanEuclidPlus) that the automated assumption SWEEP flagged — a prop that EXITED 1.
  You are NOT the thing that first runs the assumption phase: the human runs `scripts/assumptions.py` as a
  no-LLM batch/loop, which materializes a `have` per `@assumption` and classifies every premise by a ladder
  (rfl → assumption → simp[zetaDelta] → linarith → nlinarith → euclid_finish@30s), tagging valid/gap. Most
  props finish with no LLM. You are invoked ONLY for the two failures the sweep can't auto-resolve: a STEP-A
  build FAILURE (almost always a `wlog … generalizing` frame break) or the FINAL combined-Main build stop.
  Fix the cause, then finish with `assumptions.py <propdir> --tag-only`. ⛔ PRIME DIRECTIVE: NEVER delete,
  clear, skip, or retype a materialized `have` — the fix is ALWAYS to ADD the (redundant) argument to the
  `wlog`/`Hsym` reduction. Invoked with a prop path, e.g. `/faithful-assumptions Book1/Prop06`.
---

# Assumption Phase REPAIR — fix a swept prop, WITHOUT ever deleting a have

You are invoked ONLY on a prop the automated assumption SWEEP flagged (exit 1). The HUMAN runs the sweep
(`assumptions.py <propdir>` in a batch, no LLM) after the map is written, human-reviewed, and
`check_steps.py --save`'d; the ladder auto-closes the trivial premises and tags valid/gap. **A `gap` is NOT
a failure** — it's a real step Phase B proves; you do nothing about gaps. The haves are ALREADY
materialized. **Do NOT re-run the phase from scratch** — you only repair, then `--tag-only`.

## ⛔ THE PRIME DIRECTIVE (the one rule you must never break)

**NEVER delete, `clear`, skip, or retype a materialized `have stepK_assumptionN`.** Every `@assumption` is
a first-class, PROVEN obligation — the premise Euclid actually uses. If a build breaks because a have sits
before a `wlog … generalizing`, the ONLY correct fix is to **add the extra (even redundant) argument to the
`wlog` reduction** so the frame accepts the have. Deleting a have is unfaithful, defeats the phase, and
doesn't even work (`--all`'s #1 FORCE / #3 PARITY hard-fail on it anyway).

## The two failures you repair

1. **STEP-A build FAILURE** (`"STEP A build FAILED"`): a materialized `have` broke Main's build — almost
   always a `wlog … generalizing X … with Hsym` frame: the have reverts into `Hsym` as an EXTRA premise, so
   the hand-written positional `exact Hsym …` is now one argument short. The sorry haves are LEFT in place.
   The error looks like:
   ```
   argument hor' has type  <the disjunction>  but is expected to have type  <the have's type, e.g. …≠…>
   ```
   → fix the frame (below), then `--tag-only`.

2. **FINAL combined-Main build STOP** (`"PERSISTED Main did NOT compile"`): the ladder classified and
   persisted the winning-tactic bodies, but the COMBINED Main doesn't compile (tags NOT written; Main left
   for review). Read the printed error tail, fix the offending body or a missing import, then `--tag-only`.
   (Rare — each probe verified its have in isolation; a combined failure is usually an import or a body that
   only closes with a different sibling's body absent.)

## Fix the frame — ADD the argument (never remove the have)

- Find the `exact Hsym …` reduction (the `wlog`'s first `·` branch) and the `obtain ⟨…⟩ := swapfig` that
  feeds it.
- Add the extra premise `Hsym` now expects, at the position matching `Hsym`'s new binder order (context
  order — the have was added after `intro …`, so its slot is after that hypothesis's slot). The premise for
  the swapped figure usually already exists in `swapfig`'s tuple (e.g. the `≠` fact); thread it in, or
  extend `swapfig`'s helper + `obtain` to produce it. It may be redundant — that is fine and expected.
- **Do not touch the `have`, its type, its `@assumption` comment, or the claim type.**

## Finish

```
python3 scripts/assumptions.py <propdir> --tag-only
```
STEP B only — re-classifies + re-tags the already-materialized haves (skips STEP A), then re-builds the
combined Main. Exit 0 → DONE (hand back to the sweep/Phase B). Still failing → the frame fix is still wrong;
iterate — **never by deleting a have.**

## Why the frame fix is safe (and deleting is not)

The frame fix is ordinary proof code — the final `check_step --all` + the Phase-C wired build verify it.
The valid/gap tag is DERIVED from the have body (any closer tactic — rfl/assumption/simp/linarith/nlinarith/
euclid_finish — ⟹ valid; `sorry` ⟹ gap), so it cannot be faked. Everything fails closed: a broken frame is
a broken build; an unbacked gap have is caught by `--all`. Deleting a have silently drops a premise Euclid
uses — hard-failed by `--all`'s #1 FORCE / #3 PARITY anyway, so it is never even a shortcut.

## Notes

- `scripts/assumptions.py` writes `scripts/assumption_tags.json` itself (do NOT hand-edit — agent-write-
  denied; it's the tag baseline, carrying the valid/gap `tag` + the graded `level`/`closed_by`). Do NOT
  re-run `check_steps.py --save`.
- Superposition `img`/`lineImg` map coincidences (`lineImg AB = DE`) crash bare `euclid_finish`; the ladder
  closes the defining-equation ones at level 3 (`simp (config := {zetaDelta := true})`). Context-dependent
  ones (`ptImg b = e`) stay gaps for Phase B. See the `euclid-superposition-img-simp-zetadelta` memory.
- Related: `/faithful-map` (produces the `@assumption` annotations) → sweep → THIS (repair flagged props) →
  `/faithful-prove` (proves the gap haves). Mechanism: the `assumption-classification-ladder` +
  `assumption-phase-design` memories + `LeanEuclidPlus/FAITHFUL.md`.
