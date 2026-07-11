import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_20_step3 (a b e : Point) (step2 : ∠ e:a:b = ∠ e:b:a) :
    ∠ e:a:b + ∠ e:b:a = ∠ e:a:b + ∠ e:a:b := by
  euclid_finish

end Elements.Book3
