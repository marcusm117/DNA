import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- sub-fact for 2.6.6: l and c (both on the vertical CE) are on the same side of the vertical BG.
   Given BG ≠ CE (step6_bgce_ne), l,c are off BG (a common point of BG and CE would force them to
   meet, contradicting BG ∦ CE). Off BG and not separable, l and c share a side. -/
theorem helper_2_6_step6_sslc (c l : Point) (CE BG : Line)
    (hlCE : l.onLine CE) (hcCE : c.onLine CE)
    (hBGneCE : BG ≠ CE)
    (hBGCE : ¬(BG.intersectsLine CE)) :
    l.sameSide c BG := by
  euclid_intros
  have hloff : ¬(l.onLine BG) := by
    by_contra hlon
    euclid_apply (intersection_lines_common_point l BG CE)
    euclid_finish
  have hcoff : ¬(c.onLine BG) := by
    by_contra hcon
    euclid_apply (intersection_lines_common_point c BG CE)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_lines_opposing l c BG CE)
  euclid_finish

end Elements.Book2
