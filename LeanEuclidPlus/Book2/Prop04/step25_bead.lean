import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.25 sub: ¬(BE.intersectsLine AD), the symmetric orientation of ¬(AD.intersectsLine BE). -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step25_bead (AD BE : Line)
    (hADBE : ¬(AD.intersectsLine BE)) :
    ¬(BE.intersectsLine AD) := by
  intro h
  euclid_apply (intersection_symm BE AD)
  euclid_finish

end Elements.Book2
