import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_1_step1 (ABC : Circle) (a b : Point) (AB : Line)
    (h_a_on_circle : a.onCircle ABC) (h_b_on_circle : b.onCircle ABC)
    (h_a_on_AB : a.onLine AB) (h_b_on_AB : b.onLine AB) (h_ab : b ≠ a) :
    a.onCircle ABC ∧ b.onCircle ABC ∧ distinctPointsOnLine a b AB := by
  exact ⟨h_a_on_circle, h_b_on_circle, h_a_on_AB, h_b_on_AB, fun h => h_ab h.symm⟩

end Elements.Book3
