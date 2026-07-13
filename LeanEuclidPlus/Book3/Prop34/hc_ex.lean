import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_34_hc_ex (b : Point) (ABC : Circle) (BC : Line)
    (hBC_int : BC.intersectsCircle ABC) :
    ∃ c : Point, c.onCircle ABC ∧ c.onLine BC ∧ b ≠ c := by
  obtain ⟨c1, c2, h1c, h1l, h2c, h2l, h12⟩ := intersections_circle_line ABC BC hBC_int
  by_cases hb1 : b = c1
  · exact ⟨c2, h2c, h2l, by rw [hb1]; exact h12⟩
  · exact ⟨c1, h1c, h1l, hb1⟩

end Elements.Book3
