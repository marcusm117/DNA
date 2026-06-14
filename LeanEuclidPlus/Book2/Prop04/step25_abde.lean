import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.25 sub: ¬(AB.intersectsLine DE), the symmetric orientation of ¬(DE.intersectsLine AB). -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step25_abde (AB DE : Line)
    (hDEAB : ¬(DE.intersectsLine AB)) :
    ¬(AB.intersectsLine DE) := by
  euclid_apply (intersection_symm DE AB)
  euclid_finish

end Elements.Book2
