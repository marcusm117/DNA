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
