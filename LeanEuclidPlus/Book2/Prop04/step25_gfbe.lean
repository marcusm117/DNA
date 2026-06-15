import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.25 sub: g.sameSide f BE. g and f both lie on CF, which is parallel to BE (¬BE.intersectsLine
   CF) and distinct from it. Both are off BE, so two points on CF lie on the same side of BE. -/
theorem helper_2_4_step25_gfbe (g f : Point) (CF BE : Line)
    (hgCF : g.onLine CF) (hfCF : f.onLine CF)
    (hCFBE : CF ≠ BE) (hCFnBE : ¬(CF.intersectsLine BE)) :
    g.sameSide f BE := by
  euclid_intros
  have hgoff : ¬(g.onLine BE) := by
    intro hon; euclid_apply (intersection_lines_common_point g BE CF); euclid_finish
  have hfoff : ¬(f.onLine BE) := by
    intro hon; euclid_apply (intersection_lines_common_point f BE CF); euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing g f BE CF)
  euclid_apply (intersection_symm BE CF)
  euclid_finish

end Elements.Book2
