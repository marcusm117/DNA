import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

-- The circle AEB with centre F, radius FA — centre and both endpoints on it.
theorem helper_3_33_step21
    (a b f : Point) (α : Circle)
    (hfcen : f.isCentre α) (hacirc : a.onCircle α) (hb_circ_2 : b.onCircle α) :
    f.isCentre α ∧ a.onCircle α ∧ b.onCircle α := by
  exact ⟨hfcen, hacirc, hb_circ_2⟩

end Elements.Book3
