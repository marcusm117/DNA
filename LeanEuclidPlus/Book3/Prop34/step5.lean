import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_34_step5 (a b c f d1 d d2 : Point)
    (step3 : ∠ f:b:c = ∠ b:a:c) (step4 : ∠ f:b:c = ∠ d1:d:d2) :
    ∠ b:a:c = ∠ d1:d:d2 := by rw [← step3]; exact step4

end Elements.Book3
