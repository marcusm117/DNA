import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_20_step5 (a b e f : Point)
    (step2 : ∠ e:a:b = ∠ e:b:a) (step4 : ∠ b:e:f = ∠ e:a:b + ∠ e:b:a) :
    ∠ b:e:f = ∠ e:a:b + ∠ e:a:b := by
  euclid_finish

end Elements.Book3
