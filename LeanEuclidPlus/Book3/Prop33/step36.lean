import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

-- The circle of centre G, radius GA, goes through B as well as A.
theorem helper_3_33_step36
    (a b : Point) (α : Circle)
    (hacirc : a.onCircle α) (hb_circ : b.onCircle α) :
    a.onCircle α ∧ b.onCircle α := by
  exact ⟨hacirc, hb_circ⟩

end Elements.Book3
