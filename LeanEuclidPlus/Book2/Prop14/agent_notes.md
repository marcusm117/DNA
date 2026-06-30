# Prop14 (Euclid II.14 — quadrature) — agent notes

## Status
- Phase A (Main) REPAIRED by agent (the Phase-A draft did not elaborate — see "What was broken" below).
  `check_step Book2/Prop14 --provable` GREEN (Main elaborates, all `:= by sorry`).
- **Phase B COMPLETE (2026-06-30): all 22 Main nodes (fp + step1–21) --subtree-certified;
  criterion-3 deps ✓, no orphans ✓.** ONLY remaining --check item is the pre-existing
  `template/Main.lean` (missing set_option + defines a clashing proposition_14) — must be moved
  OUT of the lake module path before the final `--all`/Phase C (see TODO). NOT a pipeline file.

### Phase-B decisions (NEW — flag at gate-A re-save)
7. **step9 construction fix (Main edit).** The old `intersections_circle_line BHF ED as (h,h')`
   gave an ARBITRARY intersection, so `¬between e h d` (step9, "DE produced to H") was UNPROVABLE
   (H could be the d-side point when BE<ED). Swapped to
   `intersection_circle_line_extending_points BHF ED e d as h` → yields `between h e d` directly
   (H is the faithful "produced beyond E" point). More faithful AND makes step9 provable. (Approved.)
8. **Unconditional construction ⟹ internal case-splits, NOT BE>ED hypothesis.** Euclid's "Let BE be
   greater" was not encoded (the construction is unconditional). step11 (II.5) and step14 (Pythagoras)
   would need BE>ED, but instead are proven for EITHER ordering by SYMMETRY:
   - step11: `proposition_5` is symmetric under b₀↔f (equal cut), so case-split on `between b₀ g e`
     and apply II.5 with b₀↔f in the other branch (+ trivial e=g).
   - step14: case-split on e=g (degenerate: segment symmetry) vs e≠g (Pythagoras). Decomposed into
     step14_ss (d.sameSide c₀ BE), step14_rt0 (∠b₀:e:h=∟ via right_angle_cointerior + perpendicular_onlyif),
     step14_hoff (¬h.onLine BE from ∠b₀:e:h=∟), step14_pyth (the equation; case-split + inline perp
     transfer via equal_angles/perpendicular_onlyif + proposition_47). **by_cases lives INSIDE the
     step14_pyth LEAF, never in the step14 CONTAINER** — wiring a sorry-have-node nested in a container's
     by_cases branch produced a splicing FAIL (SP); keep container by_cases-free.
9. **KEY tooling lessons:** (a) bundling `≠` subgoals in an anonymous `⟨_,_,by euclid_finish⟩` made
   euclid_finish search & timeout — split each `≠` into its own `have := by euclid_finish` (they ARE
   entailed). (b) `fp : formParallelogram` is destructured into atoms by euclid_intros, so step18 takes
   the ATOMS and rebuilds formParallelogram in-body (unfold + euclid_finish) + explicit `∠e:b₀:c₀=∟`
   before `rectangle_area`. (c) Main edits re-stale ALL earlier nodes → had to re-`--drive` fp..step14.

## ⚠️ CRITICAL structural lesson (cost hours — read before touching Main's shape)
The conditional steps (2/3/4) and the BE>ED case need a case split, but:
1. **`→` (implication) claim types do NOT wire** — `euclid_apply` of an implication-typed helper
   leaves the antecedent as an un-dischargeable goal (Book1/Prop06 never uses `→` claims; it does
   `intro`/`by_cases` *in the proof body*). So step2/3/4 must be UNCONDITIONAL claims.
2. **The heavy construction (10 `euclid_apply`s for the semicircle) MUST be flat/unconditional,
   NOT inside a `by_cases` branch.** Symptom: `--provable` passes, but `--subtree fp` (or ANY
   node) fails with the `≠` branch's goal unsolved (`case neg.intro.intro…`, `⊢ ∃ e h, …`).
   Both top-level `by_cases` AND a `by_cases` nested in `have hwitness` fail identically.
   FIX (what works): construction UNCONDITIONAL + flat; the case discussion (step2/3/4) nested in
   a light `have hcase : True := by by_cases heq; · (step2;step3;trivial); · (step4;trivial)`.
   Reason it works: the witness `(e,h)` is the SAME in both cases (the geometric mean holds whether
   BE=ED or not), so the main goal closes unconditionally with `exact ⟨e, h, step21⟩` — no goal
   split, no heavy construction in a branch. Verified: `fp` + `step1` certify cleanly this way.

## DECISIONS MADE (flag to human at gate A re-save)
1. **A IS A QUADRILATERAL, cite [Prop. 1.45] (REVISED 2026-06-30 — supersedes the old triangle/1.42 plan).**
   Phase-C `check_faithful.sh` FAILED: text-faithfulness (criterion-1) requires the sentence to
   reproduce Euclid VERBATIM — "[Prop. 1.45]" — but the draft had changed it to "[Prop. 1.42]" to
   match a triangle model. Euclid cites 1.45 ("parallelogram equal to a given rectilinear figure"),
   so A must be modeled as the figure 1.45 takes: a QUADRILATERAL. FIX (done):
   - signature → `(a b c q) (AB BC CQ AQ QB), formTriangle a b q AB QB AQ ∧ formTriangle b c q BC CQ QB
     ∧ a.opposingSides c QB → ∃ e h, |e─h|² = △a:b:q + △q:b:c` (= template `proposition_14'`, but A's
     4th vertex is **q** not d, to avoid clashing with the rectangle's d=D).
   - construction `proposition_42 …` → `proposition_45 a b c q p a b AB BC CQ AQ QB AP AB as (e,d,b₀,c₀,…)`.
   - sentence 2.14.1 text restored to "[Prop. 1.45]"; A's area is now `△a:b:q + △q:b:c` everywhere
     (step1/2/3/20/21 claims + conclusion). prop_45's right angle is `∠e:b₀:c₀` (= ∠c₀:b₀:e by symm),
     area output `△e:b₀:c₀ + △e:d:c₀`. Rectangle (e,d,b₀,c₀) + steps 4–19 UNCHANGED.
   - **SIGNATURE CHANGED → human must re-run check_signatures.py --save at gate.**
   - step18 closer made robust (explicit `hrect` + symmetry haves, like step2/3) — bare
     `euclid_apply rectangle_area; euclid_finish` was flaky (SMT nondeterminism on area-perm).
   STATUS: 22/22 nodes ✓, criterion-3 ✓ (resolves to Book1 prop 45), integrity ✓, no orphans ✓.
   `--all` guaranteed; ready for Phase C (`scripts/phase_c.sh Book2/Prop14`). template/Main.lean deleted.
2. **Rectangle corner names.** Euclid's rectangle labels B, E, D, C collide with the triangle's
   own `a b c` (on b, c). Renamed the rectangle's B→`b₀`, C→`c₀`; kept E→`e`, D→`d`. Triangle
   `a b c` untouched. So EVERY claim that referenced rectangle b/c now uses b₀/c₀.
3. **F is a single point.** The draft used `extend_point_longer … as f` (giving `|e─f| > |e─d|`)
   AND `proposition_3 … as f0` (giving `|e─f0| = |e─d|`), but the later claims (step7 bisects b‑f,
   step11 II.5, step18 `area = |b₀─e|·|e─f|`) all used `f` while only step6 used `f0` → F was
   inconsistent. Fixed: `ffar` = produced point (aux), `f` = Euclid's F (EF = ED, beyond E),
   used consistently by every later claim.
4. **Existential conclusion** `sorry` (old line 116) → `exact ⟨e, h, step21⟩`.
5. **Missing right-angle construction** added: `proposition_11'' a b AB as p` + `line_from_points a p as AP`,
   then `proposition_42 a b c p a b AB BC CA AP AB`.
6. **`intersection_circle_line` (singular) does not exist** — replaced with the proven pair
   `intersection_circle_line_2` (fact) + `intersections_circle_line` (two points) + `point_on_circle_onlyif`,
   mirroring `helper_14_geomean` in `template/Main.lean`.

## Construction map (Main body)
```
p        = perp foot (prop 11'' at a, ∠p:a:b = ∟)            ; AP = line a p
e d b₀ c₀ = rectangle BD via prop 42                         ; ED,B₀C₀,BE,DC = its 4 lines
   formParallelogram e d b₀ c₀ ED B₀C₀ BE DC  (right angle ∠c₀:b₀:e = ∟)
   prop42 area:  (△e:b₀:c₀).area + (△e:c₀:d).area = (△a:b:c).area
ffar     = extend_point_longer BE b₀ e (e─d)                  (between b₀ e ffar, |e─ffar|>|e─d|)
f        = prop_3 e ffar e d BE ED                            (between e f ffar, |e─f|=|e─d|)  ← Euclid's F
g        = prop_10 b₀ f BE  (midpoint: between b₀ g f, |b₀─g|=|g─f|)
BHF      = circle_from_points g b₀  (centre g)
   point_on_circle_if g b₀ f BHF  → f.onCircle
   circle_points_between b₀ f e BHF → e.insideCircle
   intersection_circle_line_2 e BHF ED → ED.intersectsCircle BHF
   intersections_circle_line BHF ED as (h, h')
   point_on_circle_onlyif g b₀ h BHF → |g─h| = |g─b₀|     (step8)
GH       = line_from_points g h
```
Line `ED` (rectangle side e‑d) is ALREADY ⟂ `BE` at the right-angle corner b₀… wait, the right
angle is at b₀; `ED` passes through e and is ⟂ `BE` because the rectangle corner at e is right.
So `ED` ⟂ `BF` ⟹ the semicircle (on `b₀f`) meets line `ED` at `h`, giving the geometric mean.

## Step recipes (planned)
- step1  area=△a:b:c ∧ ∠c₀:b₀:e=∟: parallelogram_area (claim uses b₀‑d diagonal; prop42 gives e‑c₀) + rw[hang];exact hr.
- step2  BE=ED → |b₀─e|²=△a:b:c ; step3 BE=ED → area=|b₀─e|² : rectangle_area (a=e) + opposite-sides.
- step4  BE≠ED → one greater : trichotomy.
- step5  between b₀ e f ∧ f.onLine BE ; step6 |e─f|=|e─d| : construction facts + betweenness trans.
- step7  between b₀ g f ∧ |b₀─g|=|g─f| : prop_10.
- step8  |g─h|=|g─b₀| : point_on_circle_onlyif (already derived in construction).
- step9  h.onLine ED ∧ ¬(between e h d) : intersection + geometry (the tricky one — which of h,h').
- step10 distinctPointsOnLine g h GH : line_from_points.
- step11 BE·EF + EG² = GF² [2.5] : Book2.proposition_5 (a=b₀,b=f,c=g,d=e) + betweenness b₀ g e, g e f.
- step12 |g─f|=|g─h| : radii (step8 + |g─f|=|g─b₀|).  step13..17 : pure length algebra.
- step14 HE²+EG² = GH² [1.47] : proposition_47 on △g:e:h, right angle ∠g:e:h (ED ⟂ BF at e).
- step18 area = |b₀─e|·|e─f| : rectangle_area(e,d,b₀,c₀,ED,B₀C₀,BE,DC) → |e─d|·|e─b₀|; EF=ED.
- step19 area=|h─e|² ; step20 area=△a:b:c ; step21 |e─h|²=△a:b:c : algebra from step1/16/18.

## TODO / open
- template/Main.lean: scanner flags missing `set_option` cap; also defines `Elements.Book2.proposition_14`
  (clash landmine if ever built). Not imported, so currently dead. Recommend moving it out of the lake
  module path (e.g. to a `.md`/docs) at cleanup.
- Reuse option: `helper_14_geomean`/`helper_14_product` in template could be promoted to `Helpers/`
  (then human rebuilds Helpers). Not needed yet — per-step proving works.
