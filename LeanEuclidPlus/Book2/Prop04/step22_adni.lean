import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.22 sub: ¬(AD.intersectsLine CF), the symmetric orientation of ¬(CF.intersectsLine AD). -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step22_adni (AD CF : Line)
    (hCFAD : ¬(CF.intersectsLine AD)) :
    ¬(AD.intersectsLine CF) := by
  intro h
  euclid_apply (intersection_symm AD CF)
  euclid_finish

end Elements.Book2
