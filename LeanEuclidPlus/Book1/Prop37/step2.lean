import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_37_step2 (b e : Point) (AC BE : Line)
    (h_b_BE : b.onLine BE) (h_e_BE : e.onLine BE) (h_BE_AC : ¬BE.intersectsLine AC) :
    b.onLine BE ∧ e.onLine BE ∧ ¬BE.intersectsLine AC :=
  ⟨h_b_BE, h_e_BE, h_BE_AC⟩

end Elements.Book1
