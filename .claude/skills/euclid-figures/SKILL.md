---
name: euclid-figures
description: >
  Reference of recurring System-E figure-reasoning proof RECIPES for Book-2 rectangle-decomposition
  proofs (LeanEuclidPlus): the goal-shapes that come up over and over — sameSide, point-off-a-line,
  line-distinctness, betweenness via pasch, formParallelogram/formTriangle assembly, rectangle/sum
  area, and the parallel/angle props. Consult it from `prove-euclid`'s P step when you hit one of these
  shapes: it gives the axiom CHAIN to try, NOT a lemma to import — you re-prove it against YOUR figure.
---

# Euclid figure recipes — "IF YOU NEED TO PROVE THIS, TRY THIS CHAIN"

This is a **recipe book, not a library.** The facts below (`b.sameSide g CH`, `between g l h`,
`¬c.onLine AD`, …) are FIGURE-SPECIFIC — they depend on which points/lines/construction you have, so
there is no importable lemma that fits every figure (a generic one would have to thread the whole figure
through its hypotheses, just relocating the suppliability fight). Instead, each entry tells you the
**axiom chain that has worked** for that goal-shape across the done Prop01/02/03 (and Prop04's certified leaves). You write the chain against your
own points and let the build judge it.

**How to use this (inside `faithful-prove`'s recursive SF/SP/P loop, via `prove-euclid`):**
- Hit a sub-goal whose shape matches one below → introduce it as a `have <sub> : <goal> := by sorry`
  node, then prove its backing file with the chain here. Recurse if the chain needs its own sub-facts.
- The chains are **shapes, not substitutions** — match the GEOMETRY (which line is the transversal, which
  points are off which line), not the letters. A wrong instantiation simply fails SP/P; nothing unsafe is
  committed. That is exactly why this is recipes and not copy-paste bodies.
- All the usual rules still hold (`prove-euclid`): one fact per node, ≤30s, derive-don't-assume, replace
  SMT search with explicit `euclid_apply`. These recipes ARE rule #8 (explicit application) made concrete.

Grep exact signatures in `SystemE/Theory/Inferences/{Diagrammatic,Transfer,Metric}.lean` and
`Relations.lean`. Every recipe names ≥1 real file it's drawn from — open it to see the chain in context.

---

## FAMILY 1 — point off a line  (`¬ p.onLine L`)
The bread-and-butter precondition for almost everything else (distinctness, sameSide, triangle/pgram).

- **Off a PARALLEL line** (p is on a line `M`, `M ∦ L`, so p can't be on `L`): `by_contra`, then
  `intersection_lines_common_point p L M` (a shared point forces `L`,`M` to meet — contradicting
  `M ∦ L`), `euclid_finish`. *Ref: `Book2/Prop01/step5_ss_bg_ch.lean:17-24` (the `hboff`/`hgoff` sub-haves).*
- **Off a line because being on it would EQUATE two distinct lines**: `intro hon`;
  `euclid_apply (two_points_determine_line p q L M)` to get `L = M`; `rw` it and derive a contradiction
  from the now-collapsed collinearity (e.g. a right angle that can't hold on a straight line).
  *Ref: `Book2/Prop04/step5_cnad.lean`, `Book2/Prop04/step9_knab.lean`.*
- **Off a line from a right-angle + collinearity contradiction**: `intro hon`; `euclid_finish` (the
  contradiction — e.g. `a,b,d` collinear on `AB` with `∠b:a:d = ∟` — is small enough for the solver once
  the point is forced on the line). *Ref: `Book2/Prop04/step8_dnab.lean`.*
- GOTCHA: keep the signature SLIM — these are trivial facts; a bloated context makes even `euclid_finish`
  search. If an off-line leaf times out you have a context-size problem, not a hardness problem (slim
  the hyps, don't add depth).

## FAMILY 2 — two lines distinct  (`L ≠ M`)
- **From an off-line point** (cheapest): if you already have `¬p.onLine M` and `p.onLine L`, then
  `L ≠ M` is the term `fun h => hpoffM (h ▸ hpL)`. No tactic, no search. *Ref: `Book2/Prop04/step9_par.lean:29`.*
- **OFF-BASE ANCHOR** for the `euclid_finish` route: supply a point on EACH line that sits OFF the shared
  base, so distinctness proves fast instead of searching the whole figure (e.g. `f` on `BF` off `BC`
  witnesses `BF ≠ BC`). *Ref: the `f`/`hfoffBC` binders threaded through `Book2/Prop01/step6_pgram.lean`.*
- GOTCHA: distinctness is a precondition of `proposition_30`, `formTriangle`, and most pgram assembly —
  derive the needed `L ≠ M` facts as small leaves/terms FIRST so the big call has them in hand.

## FAMILY 3 — same side of a line  (`p.sameSide q L`)
- **Two points on a line `M ∦ L`, same side of `L`** (the workhorse): prove `¬p.onLine L` and
  `¬q.onLine L` (Family 1), then `by_contra hns`; `euclid_apply (intersection_lines_opposing p q L M)`;
  `euclid_finish` (opposing across `L` would make `M` cross `L`, contradicting `M ∦ L`). Add
  `euclid_apply (intersection_symm L M)` if the non-intersection fact you hold is oriented the other way
  (`¬M.intersectsLine L` vs `¬L.intersectsLine M`). *Ref (PROVEN, full chain):
  `Book2/Prop01/step5_ss_bg_ch.lean:15-27`; also `Book2/Prop01/step6_pgram.lean:21-26`,
  `Book2/Prop03/step6_sameside.lean`, `Book2/Prop04/step9_csg.lean`.*
- **Segment endpoint on the line** (`p.sameSide q L` where one segment end is ON `L`): if `r` is on `L`,
  `between r p q` (or `between q p r`), and `p,q ∉ L`, then `euclid_apply (pasch_2 r p q L)`;
  `euclid_finish`. *Ref: `Book2/Prop04/step5_ss.lean:18-21` (`c.sameSide a BD` via `pasch_2 b c a BD`).*
- GOTCHA: `sameSide` is the lone HARD conjunct of `formParallelogram` — these are the leaves you extract
  before an area call (Family 6). Don't try to get `sameSide` out of an angle-split that itself needs it
  (circular — see prove-euclid CRUCIAL SUBTLETIES); go through betweenness/pasch instead.

## FAMILY 4 — betweenness of feet / crossing points  (`between p q r`)
The "a transversal foot / intersection point lands between two others" shape. **This is the
`between b g d`/`between b k e` shape the Prop04 agent stalled on — it is NOT hard with this chain.**
- **Crossing point of two lines lies between two points** (`q = L ∩ GH`, want `between p q r` with
  `p,r` on `GH`): show `p,r` on OPPOSITE sides of `L`, then `euclid_apply (pasch_4 p q r L GH)`;
  `euclid_finish`. Get the opposite-sides fact from a point `x` on `L` that is `between p' r'` on a base
  line: `euclid_apply (pasch_3 p' x r' L)`. *Ref (PROVEN): `Book2/Prop01/step5_btw_glh.lean:21-25`
  (`pasch_3 b e c EL` → `pasch_4 g l h EL GH`); `Book2/Prop01/step5_btw_gkl.lean`.*
- **Diagonal/interior crossing** (`between b g d`, `g = CF ∩ BD`): same chain — `b,d` opposite sides of
  `CF` (one side via `pasch_3 a c b CF` since `c` on `CF` is `between a b`; the other side a `sameSide`
  sub-node), then `pasch_4 b g d CF BD`. *Ref: `Book2/Prop04/step5_bgd.lean:22-26` (note its
  `a.sameSide d CF` is its OWN sub-node — derive the sameSide separately, Family 3).*
- GOTCHA: `pasch_3` needs the middle point ON `L` and `between` the two outer points on a base line;
  `pasch_4` needs the two outer points on OPPOSITE sides of `L` and the crossing point on both `L` and
  the line they're on. Map every precondition before calling.

## FAMILY 5 — assemble a figure  (`formParallelogram …`, `formTriangle …`)
- **`formParallelogram` — assemble, don't search.** Closing it with ONE fat `euclid_finish` over its ~10
  conjuncts (4 incidences + distinctness + the `sameSide` + two non-intersections) routinely blows 30s.
  Instead: derive the hard `sameSide` as its own sub-node (Family 3) and the `≠` facts (Family 2), then
  the incidences/distinctness are already in context — let `euclid_finish` close from atoms with nothing
  to search. (For an even tighter close, `refine ⟨…incidences…, ss_subnode, ?_, ?_⟩` and only
  `euclid_finish` the 1-2 parallel/orientation conjuncts.) *Ref (PROVEN): `Book2/Prop01/step6_pgram.lean`
  (the `hbsc` sameSide sub-have + `hgh : g ≠ h`, then `euclid_finish`); `Book2/Prop03/step6_par.lean`,
  `Book2/Prop04/step9_par.lean`.*
- **`formTriangle`** — three pairwise-distinct lines (Family 2) + the incidences, then `euclid_finish`.
  *Ref: `Book2/Prop04/step8_tri.lean`.*
- GOTCHA: REUSE a sibling's figure-fact rather than re-deriving. If an earlier step proved a
  `between`/`sameSide`/`formParallelogram` you need, take it as a HYPOTHESIS (it wires by `assumption`)
  — e.g. Prop03 step6 reuses step5's `between e d f`. Re-proving it is wasted depth.

## FAMILY 6 — area of a figure  (`rectangle_area`, `sum_parallelograms_area`)
- **`rectangle_area`** (parallelogram with a right angle → `area = side·side`): the call's
  `formParallelogram` precondition is what times out, NOT the area algebra. So DECOMPOSE first — get
  `formParallelogram` (Family 5) and the right angle (Family 7) as sub-nodes, THEN
  `euclid_apply (rectangle_area …)`; `euclid_finish`. *Ref (PROVEN): `Book2/Prop01/step6.lean:23-26`
  (step6_rangle + step6_pgram sub-haves, then `rectangle_area b g c h BF CH BC GH`);
  `Book2/Prop03/step5.lean`, `Book2/Prop03/step7.lean`.*
- **`sum_parallelograms_area`** (cut a rectangle along a vertical → 4 sub-triangles sum to the halves):
  establish every foot-`between` (Family 4) and every `sameSide` (Family 3) as sub-nodes first, then one
  `euclid_apply` per cut, then `euclid_finish` telescopes. For a TWO-cut decomposition, call it once per
  cut (outer then inner). *Ref: `Book2/Prop01/step5.lean` (two `sum_parallelograms_area` calls after 5
  sameSide + 2 betweenness sub-nodes).*
- GOTCHA: a single oversized `euclid_apply (area_axiom …)` is DECOMPOSED, never re-permuted — re-running
  the same axiom with a different vertex/line order hoping one is cheaper is the forbidden
  restate-and-hope. Extract the precondition instead.

## FAMILY 7 — parallels & angles  (the cited Book-1 props)
- **Parallel transitivity** (`¬CF.intersectsLine BE` from `CF ∥ AD` and `AD ∥ BE`): the three lines
  pairwise distinct (Family 2), then `euclid_apply (proposition_30 CF BE AD)`; `euclid_finish`.
  *Ref (PROVEN): `Book2/Prop04/step9_cfbe.lean:14-20`.*
- **Right angle from co-interior angles** (`∠b:c:h = ∟`): two parallels cut by a transversal, the
  co-interior angles sum to two right angles — `g.sameSide h BC` sub-node (Family 3), then
  `euclid_apply (proposition_29''''' g h b c BF CH BC)`; `euclid_finish` (the solver finishes the
  `∠g:b:c = ∠f:b:c = ∟` ray-rewrite). *Ref (PROVEN): `Book2/Prop01/step6_rangle.lean:24-33`.*
- **Corresponding angles** (`∠c:g:b = ∠a:d:b`): `proposition_29''''` with the transversal `sameSide`
  (Family 3) + the interior `between` (Family 4) in hand. *Ref: `Book2/Prop04/step5_corr.lean`.*
- **Isosceles: equal base angles → equal sides** (`|b─c| = |c─g|`): build `formTriangle` (Family 5),
  recast the angle equality into prop-6 base-angle orientation with `angle_symm` (a real-valued rewrite,
  `rw [hstep7, hsym]`), then `euclid_apply (proposition_6 c g b CF BD AB)`; `euclid_finish`.
  *Ref (PROVEN): `Book2/Prop04/step8.lean:32-40`.*
- GOTCHA: cross-book props collide on short names — fully-qualify `Elements.Book1.proposition_M` and
  `import Book.PropM`. A cited `[Prop.~1.M]` is only RECORDED for the dependency check when it enters via
  `euclid_apply` (never term-mode `exact`) — see `faithful-prove`'s dependency-check section.

---

## THE FINAL COMBINE — `linarith` is NOT available here
The last step of an area/length proof (conclusion = a linear combination of the per-step equations) is
NOT closed with `linarith`/`nlinarith`/`ring` — **this repo has no Mathlib import, so those are "unknown
tactic".** Close it with `euclid_finish` over the step-equations held as hypotheses (it handles the
linear chain), or a `rw [...]` chain over named `have h… := by euclid_finish` length rewrites (the
lean-closer pattern: end on a thin `rw`/`euclid_finish`, never a fat one doing three jobs). *Ref:
`Book2/Prop01/step10.lean` (euclid_finish over the 5 area-equations); `Book2/Prop03/step8.lean`
(`rw [← step5, step4, step6, step7]`).*