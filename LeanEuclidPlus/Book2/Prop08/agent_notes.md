# Prop08 Phase B notes

Status after this pass:
- `step1`, `step2`, `step3`, `step4` are subtree-certified by `python3 scripts/check_step.py Book2/Prop08 --subtree stepN`.
- `check_step --status` reports 4/29 Main nodes certified; `step5` is next.

Important `step4` pattern:
- Parent `step4.lean` is a container with `step4_cbgk` and `step4_bdkn`, then two explicit `Elements.Book1.proposition_34` applications.
- `step4_cbgk` proves `formParallelogram c b g k AB MN CH BL` with subnodes:
  - `step4_cbgk_abmn`: flips `¬MN.intersectsLine AB` to `¬AB.intersectsLine MN` via `intersection_symm`.
  - `step4_cbgk_chbl`: uses `Elements.not_intersects_trans CH AE BL`; off-line facts come from `Elements.offLine_of_right_angle` and `Elements.offLine_of_two_points`.
  - `step4_cbgk_bnek`: proves `b ≠ k` by showing `b ∉ ED` using `d,e` on `ED` and `e ∉ AB`.
  - `step4_cbgk_ss`: uses `Elements.sameSide_of_parallel_both c g CH BL`.
- `step4_bdkn` proves `formParallelogram b d k n AB MN BL DF` with analogous subnodes; `step4_bdkn_dnen` derives `b ≠ k` internally because sibling facts are not suppliable across that container.

Likely next step:
- `step5` is analogous to `step4` with `MN/g/k/n` replaced by `OP/q/r/p`, but distinctness/off-line witnesses differ. Do not mechanically copy claim types; re-run `--context step5` and subnode contexts.


## Additional progress

Certified after continuation:
- `step5` subtree: Prop. 1.34 on parallelograms `c-b-q-r` and `b-d-r-p`, analogous to `step4` but over `OP`.
- `step6` subtree: Prop. 1.36 using `step6_cbgk`, `step6_bdkn`, and `step6_cbd : between c b d`.
- `step7` subtree: parent uses `Helpers.Area.parallelogram_area'` twice plus `Elements.Book1.proposition_36'` on parallelograms `g-k-q-r` and `k-n-r-p`.

Useful `step7` details:
- `step7_gkqr` hard atoms are `CH ∦ BL`, `k ∉ OP`, `MN ∦ OP`, `k ≠ r`, and `g.sameSide q BL`.
- `step7_knrp` additionally needs its own `step7_knrp_chbl` before reusing the `k ∉ OP` proof shape; otherwise SP fails because `¬CH.intersectsLine BL` is not in the local container context.
- `MN ∦ OP` is proved through `Helpers.Parallel.not_intersects_trans MN AB OP`, with `AB ∦ OP` from `intersection_symm`, `MN ≠ AB` from `k ∉ AB`, `AB ≠ OP` from `q ∉ AB`, and `MN ≠ OP` from `k ∉ OP`.

Next:
- `step8` is the next Main node. It cites Prop. 1.43. I inspected the signature but did not create `step8.lean`; the point mapping for the complement equality should be worked out before scaffolding.


## Continuation checkpoint - step8 through step11

Certified in this pass:
- step8 subtree: Prop. 1.43 complement equality for parallelogram CP, instantiated as big parallelogram d-p-c-q with diagonal ED, side point n, and diagonal point k.
  - New outer/small parallelogram cones: step8_dpcq, step8_dnkb, copied/reoriented step8_gkqr, copied step8_knrp.
  - step8_dnp proves between d n p by Pasch: first q.sameSide c BL, then between q k d, then q.sameSide p MN, then pasch_3 q k d MN and pasch_4 d n p MN DF.
- step9 subtree: transitivity from step6, step7, step8.
- step10 subtree: packages step6, step9, step7 as the three equality-chain conjuncts.
- step11 subtree: pure arithmetic from step10 via linarith.

Implementation notes:
- step8.lean intentionally uses step8_gkqr : formParallelogram g k q r MN OP CH BL rather than the rotated Prop. 1.43 orientation; the step8 combine proves the required orientation from that claim.
- step8_knrp is copied from the certified step7_knrp cone with node names changed only.
- Next Main node is step12; no backing file has been created for it yet.


## Continuation checkpoint - step12, step13 (2026-06-27)

Certified in this pass:
- step12 subtree COMPLETE. Finished the three missing step12_gkgq_ang sub-leaves:
  - step12_gkgq_ang_qkd : between q k d  — pasch_4 q k d BL ED, with q.sameSide c BL from
    sameSide_of_parallel'(c q c CH BL) and ¬CH∥BL via proposition_30 CH BL AE (needs the three
    line-≠ derived from off-line anchors). Plus between c b d.
  - step12_gkgq_ang_kqe : between k q e  — pasch_4 k q e CH ED, with ¬k.sameSide e CH from
    pasch_3 a c b CH + a.sameSide e CH + b.sameSide k CH (sameSide_of_parallel' across CH).
  - step12_gkgq_ang_gsaed : g.sameSide a ED — TWO legs: a.sameSide c ED (pasch_2 d c a ED, between a c d)
    and g.sameSide c ED (between c g q via pasch_4 c g q MN CH using ¬c.sameSide q MN from
    between q k d + c.sameSide d MN). Takes between q k d as a hyp (it is an earlier sibling have).
- step12_gkgq_ang_qkd was SLIMMED: dropped its two unused formTriangle hyps so ALL remaining hyps are
  suppliable from Main context everywhere → it is now a REUSABLE shared between-q-k-d helper.

- step13 subtree COMPLETE (rectangle AG = MQ, mirrors step6). Uses proposition_36 a c g m m g q o
  AE CH AB MN MN OP (parallels AE∥CH, equal bases CG=GQ = step12). Cone:
  - step13_acgm : formParallelogram a m c g AE CH AB MN ; step13_mogq : formParallelogram m o g q AE CH MN OP
  - step13_amo : between a m o (pasch_4 a m o MN AE; ¬a.sameSide o MN from between q k d + a.sameSide d MN
    + o.sameSide q MN)
  - step13_mnop : ¬MN∥OP (not_intersects_trans MN AB OP) — HOISTED to container, reused by mogq & amo.
  - REUSES step12_gkgq_ang_qkd as a have-node at the step13 container level (cross-cone shared helper —
    works fine once it was slimmed).

KEY TECHNIQUE for the 2nd half (steps 13-18 mirror 6-11): the transversal order `between q k d` on ED is
needed repeatedly for vertical/horizontal betweenness + parallel-line distinctness; reuse the slimmed
step12_gkgq_ang_qkd helper rather than re-deriving. Line-≠ of parallels (MN≠AB etc.) anchors on
e∉AB (offLine_of_right_angle) and the diagonal (k≠d, q≠d from between q k d). ¬L1∥L3 transitivity =
Elements.not_intersects_trans (Helpers.Parallel) needing all three line-≠.

Next Main node: step14 (rectangle QL=RF, mirrors step7, lower band OP-EF; EF∥AB is GIVEN in context).
step7_gkqr_chbl (¬CH∥BL) and step7_knrp_bldf (¬BL∥DF) are reusable shared helpers from Main context.


## Continuation checkpoint - steps 14,15,16,17,18,19 DONE (2026-06-27)

- step14 (QL=RF, mirror step7, lower band OP-EF): prop_36' h q r l l r p f EF OP CH BL BL DF (base
  QR=RP=step5, parallels OP-EF oriented so base on OP). Reuses step7_gkqr_chbl, step7_knrp_bldf, qkd.
  New shared leaf step14_efop (¬EF∥OP via not_intersects_trans EF AB OP; EF∥AB is GIVEN). EF≠OP derived
  in the container (real have) and passed to the two parallelogram leaves (needed for l≠r/f≠p).
- step15 (MQ=QL complements in parallelogram ML, Prop 1.43, mirror step8 = HARDEST). Relabel of step8:
  column CH→AE,BL→CH,DF→BL ; row AB→MN,MN→OP,OP→EF ; diagonal ED fixed ; interior point k→q.
  Big parallelogram ML = formParallelogram k l m e BL AE MN EF (corners K,L,M,e; diagonal e-K on ED).
  prop_43 k m e l g h o r q BL AE MN EF ED CH OP. CRITICAL: needs parallelogram_area' for BOTH the
  QRHL (RHS) AND the MOGQ (LHS=step13_mogq) rectangles, because prop_43's output triangulation uses the
  g-o / r-h diagonals but the goal uses m-q / q-l diagonals (step8 only needed ONE because its LHS matched
  by pure permutation). Cone: step15_klme, step15_krgq (GR on-diag), step15_qhoe (OH on-diag; split into
  qhoe_qoffab/qhoe_eoffop/qhoe_ss because the 3 line-uniqueness+sameSide blew 45s in one leaf — use
  two_points_determine_line EXPLICITLY for line-uniqueness, it's much lighter than one big euclid_finish),
  step15_qrhl (reuses qoffab+eoffop+step14_hqbl), step13_mogq (reuse), step15_ke, step15_krl (reuses
  qoffab+eoffop; ¬k.sameSide l OP via pasch_3 e q k OP + l.sameSide e OP).
  Also SLIMMED step12_gkgq_ang_kqe (dropped formTriangle hyps) → reusable like qkd.
- steps 16,17,18: pure arithmetic (mirror 9,10,11). 16=euclid_finish from step13/14/15; 17=conjunction;
  18=linarith from step17.
- step19: = step11 restated (exact h_step11).

LESSON: line-uniqueness via euclid_finish over big context is SLOW (~15-20s each); two stacked in one
leaf → >45s. Either split into sub-leaves, or use explicit `euclid_apply (two_points_determine_line …)`.

## Continuation checkpoint - steps 20,21,22,23,28 DONE (2026-06-27)

- step20 (gnomon 8 figs = 4*AK): linarith from step11 (4sq=4CK), step18 (4rect=4AG), and step20_ak
  (AK=CK+AG). step20_ak uses sum_parallelograms_area a b m k c g AB MN AE BL (cut the big rectangle ABKM
  by c on AB and g on MN) + parallelogram_area' on CBKG (reuses step6_cbgk via h_cbgk hyp) to bridge
  triangulation. Sub-leaves step20_akpar (formParallelogram a b m k AB MN AE BL) + step20_mgk (between m g k,
  pasch_4 m g k CH MN). Reuses qkd, step7_gkqr_chbl, step6_cbgk. NOTE: needed h_q_ch in the container sig.
- step21 (AK=|ab|*|bd|): rectangle_area a b m k AB MN AE BL needs ∠a:m:k=∟ — proved via
  Elements.corresponding_angle e d k a m MN AB AE (gives ∠k:m:e=∠d:a:e=∟) + step21_ame (between a m e,
  pasch_4 a m e MN AE using between e k d from qkd+kqe) ⟹ ∠a:m:k=∟. prop_34 gives |a-m|=|b-k|; step12_bdbk
  gives |b-d|=|b-k|. KEY: orient rectangle_area so its output triangulation (area a:m:k + a:b:k) MATCHES
  the goal — avoids needing a parallelogram_area' bridge.
- step22 = step20 restated (exact). step23 = linarith from step20,step21. step28 = euclid_finish from
  step1's |(b─d)|=|(c─b)| atom (NOT the conjunction — Main destructures step1; take the atom h_bd).

REMAINING: step24 (OH square = |ac|^2), step25 (arith from 23,24), step26 (gnomon+OH = square AEFD,
  BIG figure decomposition — hardest remaining), step27 (arith from 25,26 + square AEFD=|ad|^2), step29
  (final, arith from 27,28).
- step24: OH rectangle = formParallelogram o q e h OP EF AE CH. rectangle_area o q e h OP EF AE CH with
  ∠o:e:h=∟ → area(o:h:e)+area(o:q:h)=|o-q|*|o-e|. Need |o-q|=|a-c| (prop_34 on ACQO rectangle) AND
  |o-e|=|a-c| (HARD: triangle o-e-q is right-isosceles since diagonal ED makes ∠o:e:q=∠a:e:d=45° — the
  square's diagonal bisects the right corner via isosceles ADE/prop_5 with h_ae_eq |a-e|=|a-d|; then
  prop_6 gives |o-e|=|o-q|). ∠o:e:h=∟ from ∠a:e:f=∟ (square corner at e).
- step26: whole square AEFD = the 9 pieces. Likely several sum_parallelograms_area/sum_areas applications.

## STATE after this session: steps 1-23 + 28 ALL certified (24/29). Remaining: 24, 25, 26, 27, 29.

Detailed recipes for the remaining 5 (all chain: 25←23,24 ; 27←25,26 ; 29←27,28):
- **step24** (OH square = |ac|^2): rectangle_area o q e h OP EF AE CH (a_p=o,b_p=q,c_p=e,d_p=h;
  ∠o:e:h=∟) → area(o:e:h)+area(o:q:h)=|o-q|*|o-e|. Sub-leaves needed:
    · step24_ohpar : formParallelogram o q e h OP EF AE CH (o.sameSide e CH via AE∥CH; q≠h via ¬EF∥OP;
      reuse efop).
    · step24_oeh : ∠o:e:h=∟ — = ∠a:e:f=∟ (square corner) via ray ids: need between a o e (o between a,e
      on AE, like step21_ame but o) AND between e h f (h between e,f on EF). corresponding-angle or
      direct ray-equality euclid_finish once those betweens are in hand.
    · step24_oqac : |o-q|=|a-c| — prop_34 on rectangle ACQO = formParallelogram a c o q AB OP AE CH.
    · step24_oeoq : |o-e|=|o-q| — right-isosceles △oeq (formTriangle o e q AE ED OP): ∠o:e:q=∠a:e:d
      (o on ray e-a, q on ray e-d, both via betweenness on AE/ED) and ∠a:e:d=∟/2 from prop_5 on isosceles
      △ADE (|a-e|=|a-d|=h_ae_eq) + angle-sum; right angle ∠e:o:q=∟ (AE⊥OP); prop_6 ⟹ |o-e|=|o-q|.
    Then container: rectangle_area + euclid_finish with |o-q|=|a-c|, |o-e|=|o-q|.
- **step25**: linarith from step23 (4|ab||bd| = gnomon-8) and step24 (OH=|ac|^2). claim = gnomon-8 + OH.
- **step26** (gnomon-8 + OH = square AEFD = area(a:e:f)+area(a:f:d)): the BIG total decomposition — the
  whole square AEFD partitions into all 9 figures. Expect repeated sum_parallelograms_area / sum_areas_if
  over the grid (rows AB-MN-OP-EF × cols AE-CH-BL-DF). This is the largest remaining cone; budget like step15.
- **step27**: from step25 (=...= gnomon+OH) and step26 (gnomon+OH = area AEFD) and square AEFD=|ad|^2
  (rectangle_area on AEFD square, or area(a:e:f)+area(a:f:d)=|a-d|*|a-d| since side|a-e|=|a-d|). linarith/euclid_finish.
- **step29**: from step27 (4|ab||bd|+|ac|^2=|ad|^2) and step28 (|bd|=|bc|) and |ad|=|ab|+|bd| (between a b d):
  substitute → 4|ab||bc|+|ac|^2 = (|ab|+|bc|)^2. euclid_finish/ring with the length identities.

Reusable shared helpers established this session (slimmed, Main-suppliable): step12_gkgq_ang_qkd (between q k d),
step12_gkgq_ang_kqe (between k q e), step7_gkqr_chbl (¬CH∥BL), step7_knrp_bldf (¬BL∥DF), step13_mnop (¬MN∥OP),
step14_efop (¬EF∥OP), step15_mnef (¬MN∥EF), step15_qhoe_qoffab (¬q.onLine AB), step15_qhoe_eoffop (¬e.onLine OP),
step6_cbgk, step12_bdbk, step13_mogq, step14_hqbl. Pattern: line-≠ anchors on e∉AB + the diagonal order;
use two_points_determine_line EXPLICITLY (not big euclid_finish) for line-uniqueness to stay <30s.

## Continuation checkpoint — steps 24,25,27,29 DONE; step26 in progress (2026-06-27)

STATE: 28/29 Main nodes certified. ONLY step26 remains. step27 + step29 done first (independent
arithmetic — their hyps are Main-present claims, so order-rule's stability concern doesn't apply):
- **step27** (4|ab||bd|+|ac|²=|ad|²): container + leaf `step27_sq` (△aef+△afd = |ad|² via
  rectangle_area a d e f, square formPar proven inline). CRITICAL GOTCHA: euclid_finish FAILS with
  "[Smt.Translator] Improper numeric" whenever a *product* term (|ad|*|ad|, 4*(|ab|*|bd|)) sits in a
  *hypothesis* (h_step25 has products). So the SMT work (formPar + rectangle_area) is ISOLATED in
  step27_sq whose context is product-FREE (only the product GOAL, which the translator accepts), and
  step27.lean itself just `linarith`s over step25/step26/step27_sq. Products-as-atoms are fine for linarith.
- **step29** (4|ab||bc|+|ac|²=(|ab|+|bc|)²): PURE term/rw, NO euclid_finish. `between_if a b d h_abd`
  gives |ab|+|bd|=|ad| (segment addition); then `rw [← h_step28, h_ad_bd]; exact h_step27`. No SMT →
  product-hyps harmless. Only needs objects a b c d + h_abd + h_step27 + h_step28.

**step26 (the BIG tiling) — structure is SOUND (SF+SP+Combine pass); sub-nodes in progress.**
Container `step26.lean` has 21 have-nodes + `linarith`. The 8 `sum_parallelograms_area` cuts are stated
in CANONICAL vertex-orders that (a) chain perfectly and (b) match the goal's exact cell triangulations,
so the final linarith closes with NO area_symm/bridge hyps needed in the container. The canonical equalities:
```
sq1:  △a:e:f + △a:f:d = (△a:m:n + △a:n:d) + (△m:n:f + △m:f:e)        -- square cut by MN
sq2:  △m:n:f + △m:f:e = (△m:n:p + △m:p:o) + (△o:p:f + △o:f:e)        -- upper region cut by OP
btm1: △a:m:n + △a:n:d = (△a:c:g + △a:g:m) + (△c:g:n + △c:n:d)        -- bottom strip cut by CH
btm2: △c:g:n + △c:n:d = (△g:c:b + △g:b:k) + (△k:b:d + △k:d:n)        -- bottom-rest cut by BL
mid1: △m:n:p + △m:p:o = (△m:g:q + △m:q:o) + (△g:q:p + △g:p:n)        -- mid strip cut by CH
mid2: △g:q:p + △g:p:n = (△g:k:r + △g:r:q) + (△k:n:p + △k:p:r)        -- mid-rest cut by BL
top1: △o:p:f + △o:f:e = (△o:q:h + △o:h:e) + (△q:h:f + △q:f:p)        -- top strip cut by CH
top2: △q:h:f + △q:f:p = (△q:r:l + △q:l:h) + (△r:p:f + △r:f:l)        -- top-rest cut by BL
```
Each cut backing file: prove the intermediate formParallelogram INLINE (~4 have's, like step13_acgm),
take the 2 betweenness facts as HYPS, `euclid_apply (sum_parallelograms_area <par> <e> <f> <4 lines>)`
then `euclid_finish` (normalizes the raw conclusion's vertex-perms to the canonical goal). The
parallelogram vertex order for sum_parallelograms_area a b c d e f is a-b/c-d = the two sides carrying
the cut points, a-d_arg = the diagonal whose 2 halves appear on the RHS — re-derive per cut (worked
out above; e.g. sq1 uses `sum_parallelograms_area a e d f m n AE DF AB EF`).

Container reused have-nodes (already proven, SP-pass at step26): step12_gkgq_ang_qkd, step12_gkgq_ang_kqe
(diagonal ED order — NOT in Main, must re-derive as have-nodes BEFORE the parallel helpers that need them),
step15_mnef (¬MN∥EF), step13_mnop (¬MN∥OP), step21_ame (between a m e). NOTE step13_amo is NOT usable
(needs h_mnop ¬MN∥OP not Main-suppliable) — use a fresh step26_moe for between m o e instead.

NEW betweenness leaves needed (9): dnf, npf, moe, mgn, gkn, oqp, qrp, ehf, hlf. Template = step26_dnf
(CERTIFIED): mirror of step21_ame — `offLine_of_right_angle` anchor, derive between e X d (X = k on MN
or q on OP) from qkd/kqe, `pasch_3 e X d <line>` (X.onLine <line>), then `¬<a-side>.sameSide <f-side>
<line>` via euclid_finish using the parallel fact (EF∥MN from step15_mnef for dnf; analogously EF∥OP =
step14_efop for npf/top; MN∥OP = step13_mnop), then `pasch_4 <lo> <pt> <hi> <line> <ptline>`.
⭐ intersectsLine is NOT defeq-symmetric — match the helper's orientation EXACTLY (step15_mnef gives
¬(MN.intersectsLine EF), so the hyp is ¬(MN.intersectsLine EF), not ¬(EF.intersectsLine MN)).
step26_dnf DONE. Remaining 8 betweenness + 8 cuts to write. Each cut also needs the inline formParallelogram
for its strip/rest-piece (a d m n / c d g n / m n o p / g n q p / o p e f / q p h f / a e d f / m e n f).

