import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.8 sub-sub: l.sameSide c BF. l and c are both on CE (∥ BF, hCEBF). Neither can be on BF
   (if l∈BF then CE∩BF≠∅, contradicting hCEBF). So both off BF and on the same side of BF. -/
theorem helper_2_5_step8_cmpar_flip_lss (c l : Point) (CE BF : Line)
    (hlCE : l.onLine CE) (hcCE : c.onLine CE)
    (hCEBF : ¬(CE.intersectsLine BF)) :
    l.sameSide c BF := by
  euclid_intros
  have hloff : ¬(l.onLine BF) := by
    intro hon
    exact hCEBF (by euclid_apply (intersection_lines_common_point l CE BF); euclid_finish)
  have hcoff : ¬(c.onLine BF) := by
    intro hon
    exact hCEBF (by euclid_apply (intersection_lines_common_point c CE BF); euclid_finish)
  by_contra hns
  euclid_apply (intersection_lines_opposing l c BF CE)
  euclid_finish

end Elements.Book2
