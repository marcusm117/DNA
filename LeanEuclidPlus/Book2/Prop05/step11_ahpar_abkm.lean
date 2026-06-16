import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.11 sub: AB ∥ KM. From hKMAB : ¬(KM.intersectsLine AB) by symmetry. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step11_ahpar_abkm (AB KM : Line)
    (hKMAB : ¬(KM.intersectsLine AB)) :
    ¬(AB.intersectsLine KM) := by
  exact intersection_symm hKMAB

end Elements.Book2