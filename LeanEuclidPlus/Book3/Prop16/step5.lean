import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

theorem helper_3_16_step5
    (d a c : Point)
    (step3 : ∠ d:a:c = ∠ a:c:d)
    (step4 : ∠ d:a:c = ∟)
    : ∠ a:c:d = ∟ := by
  exact step3.symm.trans step4

end Elements.Book3
