import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_16_step9
    (a : Point) (ABC : Circle) (AE : Line)
    (left_1 : a.onCircle ABC)
    (left_5 : a.onLine AE)
    (step8 : ¬AE.intersectsCircle ABC)
    : ¬(∃ c : Point, c.onLine AE ∧ c.onCircle ABC ∧ c ≠ a) := by
  intro ⟨c, hcAE, hcABC, hcne⟩
  have ha_not_out : ¬a.outsideCircle ABC := fun h => h.2 left_1
  have hc_not_out : ¬c.outsideCircle ABC := fun h => h.2 hcABC
  obtain ⟨m, hmAE, hbetween⟩ := exists_point_between_points_on_line AE a c ⟨left_5, hcAE, hcne.symm⟩
  have hm_inside : m.insideCircle ABC := circle_points_between a c m ABC ⟨ha_not_out, hc_not_out, hbetween⟩
  exact step8 (intersection_circle_line_2 m ABC AE ⟨hm_inside, hmAE⟩)

end Elements.Book3
