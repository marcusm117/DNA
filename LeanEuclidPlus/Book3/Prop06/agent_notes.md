# Book3/Prop06 (III.6) — Phase B notes

## BLOCKER (2026-07-06): signature is missing `ABC ≠ CDE` — theorem not valid as stated

**Finding:** `step7 : False` is NOT derivable from the current map's context.
`euclid_finish` with the full axiom set cannot close it. Empirically verified in
`step7.lean`:
- context as-is → `Could not prove: False`
- add `hbet : between f e b` → closes (but betweenness is NOT derivable / is
  inconsistent with `|fe|=|fb|` under a common centre; its ¬-branch is satisfiable)
- add `hne : ABC ≠ CDE` → **closes cleanly via `equal_circles`**, no betweenness needed.

**Why:** with a *common* centre, `equal_circles` (f centre both, b on ABC, c/e on CDE,
`|fb|=|fc|`/`|fe|=|fb|`) forces `ABC = CDE` (equal radii). The "FE = FB, the lesser to
the greater" impossibility, rendered in System E, IS exactly "the two radii are equal ⇒
the circles coincide ⇒ contradicts that they are two distinct circles."

**Counterexample to the current statement:** take `CDE := ABC` (the same circle). Then
`∃c, c.onCircle ABC ∧ c.onCircle CDE` (any point), `¬ABC.intersectsCircle CDE` (a circle
doesn't cross itself), `f.isCentre ABC ∧ f.isCentre CDE` — all hypotheses hold, goal
`False` does not. So `proposition_6` is under-specified.

**Fix (Phase-A, human-gated — I am hard-denied editing `proposition_6`):** add
`ABC ≠ CDE` as a hypothesis (faithful: "two circles touch one another" ⇒ two *distinct*
circles). Then step7 needs no betweenness and no `@euclid_gap`. Open sub-question: encode
distinctness in III.6's signature only, or bake `α ≠ β` into the circle–circle `touches`
convention in BOOK3_VOCAB_PRIMER.md globally (III.11/12/13 likely have the same issue;
III.5's twin uses `intersectsCircle` and may get distinctness for free — not checked).

`step7.lean` currently carries `(hne : ABC ≠ CDE)` and passes P — it documents the exact
fix. It will only be SP-suppliable once the signature provides `ABC ≠ CDE`.

**RESOLVED 2026-07-06:** operator chose "III.6 signature only". Added `ABC ≠ CDE →` as a
separate hypothesis arrow to `proposition_6` (keeps `left`/`right` destructuring intact).
Main re-elaborates. `a✝ : ABC ≠ CDE` now in every node's context. step7 closes via
`equal_circles` (no betweenness, no gap).
**HUMAN TODO at Phase C:** `check_steps.py --save Book3/Prop06/Main.lean` +
`check_signatures.py --save` (baselines drifted by the signature edit; I'm `--save`-denied).

## step7 — DONE: `equal_circles` route
`|fe|=|fb|` (step6) + b on ABC + e on CDE + f centre both ⇒ ABC=CDE, contradicts ABC≠CDE.
euclid_finish finds it with the distinctness hyp in context.

## hFEB construction restructured (2026-07-06)

Phase-A map built the line via `have hFEB : ∃ b e FEB, … := by sorry; obtain …`. That
existential-`have` construction node does NOT wire: `euclid_apply (helper)` on an
∃-concluding helper obtains witnesses but cannot CLOSE an ∃ goal (SP syntax-errored). No
vetted done prop uses that shape — Prop01 constructs objects via `euclid_apply (…) as (…)`.
Replaced (claims frozen — step3–6 untouched) with:
```
euclid_apply (exists_point_on_circle ABC) as b
euclid_apply (line_from_points f b) as FEB
have hFEB_int : FEB.intersectsCircle CDE := by sorry   -- backing node
euclid_apply (intersections_circle_line CDE FEB) as (e, e2)
```
`hFEB_int` proved by `center_inside_circle f CDE` (f interior) + `intersection_circle_line_2`.
Node list is now: step1, step2, hFEB_int, step3, step4, step5, step6, step7, step8.
(`hFEB.lean` deleted.) This Main edit re-stales step1/step2 — re-drive.

Proving order: step1✓ step2✓ hFEB_int✓ step3✓ step4✓ step5✓ step6✓ step7✓ step8✓.

## Phase B COMPLETE (2026-07-06)
All 9 nodes certified (--drive green, --check + --dependency clean). Final --all launched.
Node recipes:
- step1/step2/step3: repackage context facts (⟨…⟩).
- hFEB_int: `center_inside_circle f CDE` + `intersection_circle_line_2` + assumption.
- step4/step5: `point_on_circle_onlyif` (radii of ABC / CDE) + euclid_finish.
- step6: euclid_finish (transitivity of step5 + @assumption).
- step7: euclid_finish via `equal_circles` (needs ABC≠CDE) — the "lesser=greater" impossibility.
- step8: `exact habsurd1` (reductio_close restates the outer reductio have).

## HUMAN Phase-C TODO
1. `check_steps.py --save Book3/Prop06/Main.lean` + `check_signatures.py --save` — BOTH baselines
   drifted (signature gained `ABC ≠ CDE`; step map lost `hFEB`, gained `hFEB_int`). REQUIRED.
2. `wire_main.py Book3/Prop06` + `check_faithful.sh Book3`.
NOTE the signature change (`ABC ≠ CDE`) is a genuine correctness fix, not cosmetic — the old
statement was falsifiable (CDE=ABC). Consider whether III.5/11/12/13 need the same audit.
