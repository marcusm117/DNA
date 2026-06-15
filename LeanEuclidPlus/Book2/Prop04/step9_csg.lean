import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.9 sub: c.sameSide g BE. c and g both lie on CF, which is parallel to BE (¬CF.intersectsLine
   BE). Both are off BE (a shared point would make CF meet BE, as CF ≠ BE), and two points on a line
   parallel to BE lie on the same side of BE. -/
theorem helper_2_4_step9_csg (c g : Point) (CF BE : Line)
    (hcCF : c.onLine CF) (hgCF : g.onLine CF)
    (hCFBE : CF ≠ BE) (hCFBEp : ¬(CF.intersectsLine BE)) :
    c.sameSide g BE := by
  euclid_intros
  have hcoff : ¬(c.onLine BE) := by
    intro hon; euclid_apply (intersection_lines_common_point c CF BE); euclid_finish
  have hgoff : ¬(g.onLine BE) := by
    intro hon; euclid_apply (intersection_lines_common_point g CF BE); euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing c g BE CF)
  euclid_apply (intersection_symm BE CF)
  euclid_finish

end Elements.Book2
