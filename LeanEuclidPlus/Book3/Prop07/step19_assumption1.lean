import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_7_step19_assumption1
    (ABCD : Circle) (e g h : Point)
    (h_ctr : e.isCentre ABCD)
    (hg : g.onCircle ABCD)
    (hh_on : h.onCircle ABCD)
    : |(e─g)| = |(e─h)| := by
  euclid_finish

end Elements.Book3
