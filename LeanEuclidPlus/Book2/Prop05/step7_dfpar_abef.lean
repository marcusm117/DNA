import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- ¬(AB.intersectsLine EF): flip hEFAB via intersection_symm. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step7_dfpar_abef (AB EF : Line)
    (hEFAB : ¬(EF.intersectsLine AB)) :
    ¬(AB.intersectsLine EF) := by
  intro hx
  euclid_apply (intersection_symm AB EF)
  euclid_finish

end Elements.Book2
