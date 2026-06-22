import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step6_bdkn_abmn (AB MN : Line)
    (h_mn_ab : ¬(MN.intersectsLine AB)) :
    ¬(AB.intersectsLine MN) := by
  intro h
  euclid_apply (intersection_symm AB MN)
  euclid_finish

end Elements.Book2
