import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.11 sub: AB ∥ KM. From hKMAB : ¬(KM.intersectsLine AB) by symmetry. -/
theorem helper_2_5_step11_ahpar_abkm (AB KM : Line)
    (hKMAB : ¬(KM.intersectsLine AB)) :
    ¬(AB.intersectsLine KM) := by
  intro hint
  euclid_apply (intersection_symm AB KM)
  euclid_finish

end Elements.Book2
