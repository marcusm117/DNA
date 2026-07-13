import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_35_step13 (b c f : Point) (ABCD : Circle)
  (hb : b.onCircle ABCD) (hc : c.onCircle ABCD) (hfc : f.isCentre ABCD)
  : |(f─c)| = |(f─b)| := by
  euclid_finish

end Elements.Book3
