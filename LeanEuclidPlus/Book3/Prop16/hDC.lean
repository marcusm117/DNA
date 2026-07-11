import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

theorem helper_3_16_hDC
    (d c : Point) (ABC : Circle)
    (left : d.isCentre ABC)
    (hcABC : c.onCircle ABC)
    : ∃ DC : Line, d.onLine DC ∧ c.onLine DC := by
  have hd_inside : d.insideCircle ABC := center_inside_circle d ABC left
  have hd_not_on : ¬d.onCircle ABC := inside_not_on_circle d ABC hd_inside
  have hdc : d ≠ c := fun h => hd_not_on (h ▸ hcABC)
  obtain ⟨DC, hd, hc⟩ := line_from_points d c hdc
  exact ⟨DC, hd, hc⟩

end Elements.Book3
