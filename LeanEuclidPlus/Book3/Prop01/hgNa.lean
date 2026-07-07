import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_1_hgNa (ABC : Circle) (a g : Point)
    (h_a_on : a.onCircle ABC) (h_g_center : g.isCentre ABC) :
    g ≠ a := by
  intro h_eq
  have h_g_inside : g.insideCircle ABC := center_inside_circle g ABC h_g_center
  have h_g_not_on : ¬(g.onCircle ABC) := inside_not_on_circle g ABC h_g_inside
  exact h_g_not_on (h_eq.symm ▸ h_a_on)

end Elements.Book3
