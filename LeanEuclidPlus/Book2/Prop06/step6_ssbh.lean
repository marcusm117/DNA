import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- sub-fact for 2.6.6 / step6_klh: b and h (both on the vertical BG) are on the same side of CE.
   Given BG ≠ CE, b,h are off CE (a common point of BG and CE would force them to meet, contradicting
   BG ∦ CE). Off CE and not separable, b and h share a side. -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step6_ssbh (b h : Point) (CE BG : Line)
    (hbBG : b.onLine BG) (hhBG : h.onLine BG)
    (hBGneCE : BG ≠ CE)
    (hBGCE : ¬(BG.intersectsLine CE)) :
    b.sameSide h CE := by
  euclid_intros
  have hboff : ¬(b.onLine CE) := by
    by_contra hbon
    euclid_apply (intersection_lines_common_point b CE BG)
    euclid_finish
  have hhoff : ¬(h.onLine CE) := by
    by_contra hhon
    euclid_apply (intersection_lines_common_point h CE BG)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_lines_opposing b h CE BG)
  euclid_finish

end Elements.Book2
