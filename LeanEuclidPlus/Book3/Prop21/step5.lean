import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_21_step5
    (a b d e f' : Point)
    (step3 : ∠ b:f':d = ∠ b:a:d + ∠ b:a:d)
    (step4 : ∠ b:f':d = ∠ b:e:d + ∠ b:e:d) :
    ∠ b:a:d = ∠ b:e:d := by
  euclid_finish

end Elements.Book3
