import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

-- Let the circle go like AEB: centre G, and A, B, H all on it.
theorem helper_3_33_step37
    (a b g h : Point) (α : Circle)
    (hgcen : g.isCentre α) (hacirc : a.onCircle α) (hb_circ : b.onCircle α) (hh_circ : h.onCircle α) :
    g.isCentre α ∧ a.onCircle α ∧ b.onCircle α ∧ h.onCircle α := by
  exact ⟨hgcen, hacirc, hb_circ, hh_circ⟩

end Elements.Book3
