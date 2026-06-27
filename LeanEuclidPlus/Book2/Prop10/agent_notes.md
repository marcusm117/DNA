# Prop10 (Euclid II.10) — Phase B notes

II.10 is the **same figure as Prop09 (II.9)** but D is OUTSIDE AB (`between a b d`), so it adds
(a) a Post-5 "the lines EB, FD meet" argument (sentences 6–10) and (b) a lower-triangle DBG/BDG/DGB
chain (sentences 16–20). The square-algebra tail (24–41) mirrors Prop09 closely.

## Certified so far (each `check_step Book2/Prop10 stepN` = SF+SP+P PASS)
- step1 — ∠a:c:e=∟ — mirror of Prop09 step1 (`equal_angles c a a e e0 AC' CE`), AB→AD.
- step2 — |ce|=|ac| ∧ |ce|=|cb| — mirror Prop09 step2 (euclid_finish from prop-3 cut + |ac|=|cb|).
- step3 — distinctPointsOnLine e a EA ∧ … e b EB — mirror Prop09 step3 (inline `offLine_of_two_points`, AB→AD).
- step4 — e∈EF ∧ ¬EF∩AD — trivial leaf (proposition_31 outputs).
- step5 — d∈FD ∧ ¬FD∩CE — trivial leaf.
- step6 — ∠c:e:f + ∠e:f:d = ∟+∟ — NEW (Post-5 setup). Leaf using:
  `proposition_29''''' c d e f CE FD EF` (co-interior sum). Preconditions derived inline:
  `e∈CE` (between_same_line_in), `e∉AD` (`offLine_of_two_points'`), `c.sameSide d EF`
  (`sameSide_of_parallel c d e AD EF`, witness e), `¬CE∩FD` (TERM: `fun h => hFDCE (intersection_symm CE FD h)`).
  GOTCHA: `intersection_symm L M : L∩M → M∩L` — to flip `¬FD∩CE` into `¬CE∩FD` use the TERM above,
  NOT `euclid_apply (intersection_symm …); euclid_finish` (that failed "Could not prove False").

## ✓ POST-5 BLOCK SOLVED (steps 7–10 certified)
- step7 ∠f:e:b+∠e:f:d<∟+∟ — RICH-CONTEXT euclid_finish (full figure + step6). The < ordering (b interior
  to ∠FEC) is derived by the SMT given the perpendicular/parallels/betweenness.
- step8 EB.intersectsLine FD — **THE MEETING. euclid_finish WORKS with rich context** (perpendicular
  ∠a:c:e0=∟, both parallels ¬EF∩AD/¬FD∩CE, betweenness, step6, step7). A THIN context (just step7 +
  bare incidences) FAILS — there is no Post-5 axiom and the named points don't straddle for
  intersection_lines_opposing, but the SMT derives the crossing from the full figure. Lesson: for a
  meeting, hand euclid_finish the WHOLE figure, not just the angle sum.
- step9 EB.intersectsLine FD — trivial: consumes step8 (`:= hmeet`).
- step10 distinctPointsOnLine a g AG — mirror Prop09 step6 (a∉EB chain, AB→AD, f→g); a≠b derived in-body
  (NOT a hyp — `between a c b` is the context atom, not `a≠b`).

## ✓ ANGLE CHAIN 11–15 certified (session 2)
- step11 ∠e:a:c=∠a:e:c — mirror Prop09 step7 (isosceles, prop_5), AB→AD.
- step12 ∠a:c:e=∟ — trivial leaf, consumes step1 (`:= hright`).
- step13 ∠e:a:c=∟/2 ∧ ∠a:e:c=∟/2 — prop_32 angle-sum + right angle + step11 equality, angle_symm + linarith.
- step14 ∠c:e:b=∟/2 ∧ ∠e:b:c=∟/2 — mirror Prop09 step11 (triangle CEB, prop_5+prop_32+halve), AB→AD.
- step15 ∠a:e:b=∟ — CONTAINER: sub-node step15_split (∠a:e:b=∠a:e:c+∠c:e:b, mirror Prop09 step12_split,
  AB→AD, addition only) + linarith [step13.2, step14.1].

## ⚠ RESUME AT step16 (session 3) — two GOTCHAS learned this session:
1. **∟/2 crashes the SMT translator** ("[Smt.Translator] Improper numeric") when a `∠…=∟/2` fact is in
   the euclid_finish context. FIX: prove the pure-geometry part with the ∟/2 hyp CLEARED (`clear hassump`),
   then combine via `linarith [hassump, …]`. (Same reason Prop09 uses linarith for all halving.)
2. **Conjunctive step claims are NOT auto-split in context** (step14 shows as the whole `∧`, not left/right).
   So an @assumption whose type is a CONJUNCT (e.g. ∠e:b:c=∟/2 from step14) needs `use_override stepN.2`.
   Already applied: Main's step16 @assumption now has `use_override step14.2`. (When step24/28 etc. consume
   a conjunct, same pattern.)
- **step16 BLOCKER**: vertical-angle ∠DBG=∟/2 via `proposition_15 e g c d b EB AD` (→ ∠e:b:c=∠d:b:g) needs
  `between e b g`, whose SMT discharge over the full context TIMES OUT (>45s). DECOMPOSE: sub-node
  `step16_beg : between e b g` (b=EB∩AD; e above AD, g below AD on FD ⟹ e.opposingSides g AD ⟹ crossing
  gives between e b g — look at pasch_3/pasch_4 or intersection betweenness). Then step16 = container:
  hvert (prop_15, clear hassump) + linarith. step16.lean currently a clean sorry stub with this plan inline.

## REMAINING — step16..step41 (OLD next plan below)
- step7 : ∠f:e:b + ∠e:f:d < ∟+∟ — needs FEB < CEF (ray e→b inside ∠CEF), then subtract step6.
- step8/step9 : EB.intersectsLine FD — Euclid's Post 5. **No angle-sum→meet axiom found** via
  `find.py --concludes intersectsLine` / `--grep right`. Candidates: `intersection_lines_opposing`
  (opposing-sides → intersect) or `intersection_lines_common_point`. INVESTIGATE how Post-5 / "lines
  meet" is encoded before scaffolding these two. (Both currently have the same claim `EB.intersectsLine FD`
  — flagged to human at Phase A; may merge/restructure.)
- step10 : distinctPointsOnLine a g AG — after g=intersection_lines EB FD constructed; mirror Prop09 step6 (AF) shape.

## Then step11..step41
- 11–15 isosceles/half-angle → ∠a:e:b=∟ : mirror Prop09 steps 7,8,10,11,12 (NOTE: Prop10 step12 is a
  separate sentence ∠a:c:e=∟ restating step1; step13 = both half via prop_32).
- 16–20 lower triangle (NEW): step16 ∠d:b:g=∟/2 [prop_15 supplement of EBC]; step17 ∠b:d:g=∟ [alt angles
  prop_29 from right angle at C — DERIVE in-body, not @assumption]; step18 remaining ∠d:g:b=∟/2; step19
  ∠d:g:b=∠d:b:g; step20 |bd|=|gd| [prop_6].
- 21 ∠f:e:g=∟/2 (claim conclusion-only; "angle at F right" DERIVE via prop_34); 22 ∠e:g:f=∠f:e:g; 23 |gf|=|ef| [prop_6].
- 24–41 square algebra → mirror Prop09 steps 19–39 (squares, prop_47 Pythagoras on triangles AEG/ADG,
  prop_34 for EF=CD, final telescope). Watch: step30 needs ∠ at F right (derive), step38 needs ∠ at D right (derive).

## @assumption set (frozen at gate A): step11 AC=CE, step16 EBC half, step21 EGF half, step24 EC=CA, step28 FG=EF.
Drive order: step7 next (in order). Use `check_step Book2/Prop10 --subtree stepN` to confirm a cone; `--all` ONLY at the very end.
