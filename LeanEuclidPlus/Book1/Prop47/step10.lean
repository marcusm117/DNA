import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step10
    (a b c d f : Point)
    (h_dba_fbc : ∠ d:b:a = ∠ f:b:c) :
    ∠ d:b:a = ∠ f:b:c := by
  exact h_dba_fbc

end Elements.Book1
