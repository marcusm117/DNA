import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- The circle (centre g, radius ga) goes through both a and b.
theorem helper_3_33_step10
    (a b : Point) (α : Circle)
    (hacirc : a.onCircle α) (hb_circ : b.onCircle α) :
    a.onCircle α ∧ b.onCircle α :=
  ⟨hacirc, hb_circ⟩

end Elements.Book3
