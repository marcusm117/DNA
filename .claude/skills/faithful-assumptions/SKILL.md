---
name: faithful-assumptions
description: >
  Run the ASSUMPTION PHASE for a Euclid prop (LeanEuclidPlus), between `/faithful-map` + human review
  and `/faithful-prove`. Invoke `scripts/assumptions.py <propdir>` (it materializes a `have` per
  `@assumption`, build-checks Main, then classifies each valid/gap by firing `euclid_finish` at a 3s cap
  and writes the tags). If its STEP-A build-check FAILS (almost always a `wlog … generalizing` frame
  break), FIX THE FRAME properly and finish via `--tag-only`. ⛔ PRIME DIRECTIVE: NEVER delete, clear,
  skip, or retype a materialized assumption `have` — the fix is ALWAYS to ADD the (redundant) argument to
  the `wlog`/`Hsym` reduction. Invoked with a prop path, e.g. `/faithful-assumptions Book1/Prop06`.
---

# Assumption Phase — run the script, and fix frame breaks WITHOUT ever deleting a have

Run this AFTER `/faithful-map` is written, human-reviewed, and `check_steps.py --save`'d — and BEFORE
`/faithful-prove`. It is thin on purpose: the SCRIPT does materialize + build-check + classify + tag; you
only intervene on the one specific failure (a frame break), and only ever by ADDING to the frame.

## ⛔ THE PRIME DIRECTIVE (the one rule you must never break)

**NEVER delete, `clear`, skip, or retype a materialized `have stepK_assumptionN`.** Every `@assumption`
is a first-class, PROVEN obligation — the premise Euclid actually uses. If a build breaks because a have
sits before a `wlog … generalizing`, the ONLY correct fix is to **add the extra (even redundant)
argument to the `wlog` reduction** so the frame accepts the have. Deleting the have is unfaithful, defeats
the whole phase, and does not even work (a genuine gap before a `wlog` clashes identically). If you ever
feel the urge to remove or `clear` a have — STOP; the fix is in the frame, not the have.

## The flow

1. **Run it:** `python3 scripts/assumptions.py <propdir>` (bare, from `LeanEuclidPlus/`).
   - **Exit 0** → STEP A built clean and STEP B tagged. Read the report (`X valid / Y gaps`, gap list =
     where Euclid skipped a step). **DONE** → hand to `/faithful-prove` (the `@assumption_gap` haves are
     the new `:= by sorry` nodes it proves; `@assumption_valid` haves are already done).
   - **Exit non-zero, "STEP A build FAILED"** → the materialized haves broke Main's build (STEP B did NOT
     run; the sorry haves are left in place, fail-closed). Go to step 2.

2. **Diagnose the frame break** (the script prints a hint + the Lean error tail). It is almost always a
   `wlog … generalizing X … with Hsym`: a materialized `have` before it mentions a generalized var, so
   `wlog` reverts it into `Hsym` as an EXTRA premise, and the hand-written positional `exact Hsym …` is
   now one argument short. The error looks like:
   ```
   argument hor' has type  <the disjunction>  but is expected to have type  <the have's type, e.g. …≠…>
   ```
   i.e. an argument landed in the slot of the newly-generalized have.

3. **Fix the frame — ADD the argument (never remove the have):**
   - Find the `exact Hsym …` reduction (the `wlog`'s first `·` branch) and the `obtain ⟨…⟩ := swapfig`
     that feeds it.
   - Add the extra premise `Hsym` now expects, at the position matching `Hsym`'s new binder order
     (context order — the have was added after `intro …`, so its slot is after that hypothesis's slot).
     The premise for the swapped figure usually already exists in `swapfig`'s tuple (e.g. the `≠` fact);
     thread it in, or extend `swapfig`'s helper + `obtain` to produce it. It may be redundant — that is
     fine and expected.
   - **Do not touch the `have`, its type, its `@assumption` comment, or the claim type.**

4. **Finish:** `python3 scripts/assumptions.py <propdir> --tag-only` — STEP B only (classify + tag the
   already-materialized haves; skips materialize + build-check). If it now exits 0 → DONE. If STEP B's
   classify builds still fail, the frame fix is still wrong — iterate step 3 (add/adjust the argument),
   **never by deleting the have.**

## Why the frame fix is safe (and deleting is not)

The frame fix is ordinary proof code — the final `check_step --all` + the Phase-C wired build verify it.
The valid/gap tag is DERIVED from the have body (`euclid_finish`=valid, `sorry`=gap), so it cannot be
faked. Everything fails closed: a broken frame is a broken build, an unbacked gap have is caught by
`--all`. Deleting a have, by contrast, silently drops a premise Euclid uses — `--all`'s #1 FORCE and #3
PARITY checks will hard-fail on it anyway, so it is never even a shortcut.

## Notes

- The script writes `scripts/assumption_tags.json` itself (do NOT hand-edit it — it's the tag baseline).
  Do NOT re-run `check_steps.py --save` (the phase doesn't change what it captures).
- This skill runs the real (writing) pass — that is the point of invoking it. `--dry-run` is the
  no-writes diagnostic if you only want to preview the split.
- Related: `/faithful-map` (produces the `@assumption` annotations), `/faithful-prove` (proves the gap
  haves). Mechanism reference: see the `assumption-phase-design` memory + `LeanEuclidPlus/FAITHFUL.md`.
