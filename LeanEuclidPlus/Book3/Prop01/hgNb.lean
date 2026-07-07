import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_1_hgNb (ABC : Circle) (b g : Point)
    (h_b_on : b.onCircle ABC) (h_g_center : g.isCentre ABC) :
    g ≠ b := by
  intro h_eq
  have h_g_inside : g.insideCircle ABC := center_inside_circle g ABC h_g_center
  exact inside_not_on_circle g ABC h_g_inside (h_eq.symm ▸ h_b_on)

end Elements.Book3
