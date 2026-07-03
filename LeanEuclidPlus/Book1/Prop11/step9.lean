import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_11_step9
    (a b c d e : Point)
    (hacb : between a c b)
    (hadc : between a d c) (hceb : between c e b) :
    between d c e := by
  euclid_finish

end Elements.Book1
