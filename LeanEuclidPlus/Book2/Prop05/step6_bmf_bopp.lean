import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub-sub-sub: ¬b.sameSide e DG (b and e on opposite sides of DG). d (= DG ∩ AB) is between c
   and b on AB (between c d b), so pasch_3 c d b DG gives c,b opposite across DG. e shares c's side
   (e,c on CE; DG ∥ CE ⟹ e.sameSide c DG). Opposite-of-same ⟹ b,e opposite. -/
theorem helper_2_5_step6_bmf_bopp (b c d e : Point) (AB CE DG : Line)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hdDG : d.onLine DG)
    (hcdb : between c d b) (hDGCE : ¬(DG.intersectsLine CE)) :
    ¬(b.sameSide e DG) := by
  euclid_intros
  -- c,b opposite across DG (d between them, d on DG)
  euclid_apply (pasch_3 c d b DG)
  -- e on c's side of DG (e,c on CE ∥ DG): derive e.sameSide c DG, then b opposite e
  have hcoff : ¬(c.onLine DG) := by
    intro hcon
    euclid_apply (intersection_lines_common_point c DG CE)
    euclid_finish
  have heoff : ¬(e.onLine DG) := by
    intro heon
    euclid_apply (intersection_lines_common_point e DG CE)
    euclid_finish
  have hecDG : e.sameSide c DG := by
    by_contra hns
    euclid_apply (intersection_lines_opposing e c DG CE)
    euclid_finish
  euclid_finish

end Elements.Book2
