import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.4 sub-sub: f.sameSide b CN. f and b both lie on BE, which is parallel to CN
   (¬CN.intersectsLine BE) and distinct from it. Both are off CN, so two points on BE lie on the
   same side of CN. -/
theorem helper_2_7_step4_fsb (f b : Point) (BE CN : Line)
    (hfBE : f.onLine BE) (hbBE : b.onLine BE)
    (hCNBE : CN ≠ BE) (hCNBEni : ¬(CN.intersectsLine BE)) :
    f.sameSide b CN := by
  euclid_intros
  have hBECN : BE ≠ CN := fun h => hCNBE h.symm
  have hfoff : ¬(f.onLine CN) := by
    intro hon; euclid_apply (intersection_lines_common_point f CN BE); euclid_finish
  have hboff : ¬(b.onLine CN) := by
    intro hon; euclid_apply (intersection_lines_common_point b CN BE); euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing f b CN BE)
  euclid_apply (intersection_symm CN BE)
  euclid_finish

end Elements.Book2
