import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.22 sub: b.sameSide e CF. b and e both lie on BE, which is parallel to CF (¬CF.intersectsLine
   BE) and distinct from it. Both are off CF, so two points on BE lie on the same side of CF. -/
theorem helper_2_4_step22_becf (b e : Point) (BE CF : Line)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hBECF : BE ≠ CF) (hCFBE : ¬(CF.intersectsLine BE)) :
    b.sameSide e CF := by
  euclid_intros
  have hboff : ¬(b.onLine CF) := by
    intro hon; euclid_apply (intersection_lines_common_point b CF BE); euclid_finish
  have heoff : ¬(e.onLine CF) := by
    intro hon; euclid_apply (intersection_lines_common_point e CF BE); euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing b e CF BE)
  euclid_apply (intersection_symm CF BE)
  euclid_finish

end Elements.Book2
