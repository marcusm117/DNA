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
