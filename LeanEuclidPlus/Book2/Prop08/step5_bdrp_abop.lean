import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step5_bdrp_abop (AB OP : Line)
    (h_op_ab : ¬(OP.intersectsLine AB)) :
    ¬(AB.intersectsLine OP) := by
  intro h
  euclid_apply (intersection_symm AB OP)
  euclid_finish

end Elements.Book2
