import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.9 sub: between a c d. On line AB the order is a, c, b, d (between a c b, between a b d); since
   c is between a and b, and b is between a and d, c is between a and d (between_trans_in). -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step9_acd (a b c d : Point)
    (hacb : between a c b) (habd : between a b d) :
    between a c d := by
  euclid_finish

end Elements.Book2
