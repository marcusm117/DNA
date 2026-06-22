import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.3 sub: ¬(BE.intersectsLine AD), the symmetric orientation of ¬(AD.intersectsLine BE). -/
theorem helper_2_7_step3_bead (AD BE : Line)
    (hADBE : ¬(AD.intersectsLine BE)) :
    ¬(BE.intersectsLine AD) := by
  intro h
  euclid_apply (intersection_symm BE AD)
  euclid_finish

end Elements.Book2
