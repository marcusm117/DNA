import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- The circle ABE: centre g, through a, b, e.
theorem helper_3_33_step11
    (a b e g : Point) (α : Circle)
    (hgcen : g.isCentre α) (hacirc : a.onCircle α) (hb_circ : b.onCircle α) (he_circ : e.onCircle α) :
    g.isCentre α ∧ a.onCircle α ∧ b.onCircle α ∧ e.onCircle α :=
  ⟨hgcen, hacirc, hb_circ, he_circ⟩

end Elements.Book3
