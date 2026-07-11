import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_16_step2
    (d c : Point) (ABC : Circle) (DC : Line)
    (left : d.isCentre ABC)
    (hcABC : c.onCircle ABC)
    (hDCd : d.onLine DC)
    (hDCc : c.onLine DC)
    : distinctPointsOnLine d c DC := by
  have hd_inside : d.insideCircle ABC := center_inside_circle d ABC left
  have hd_not_on : ¬d.onCircle ABC := inside_not_on_circle d ABC hd_inside
  have hdc : d ≠ c := fun h => hd_not_on (h ▸ hcABC)
  exact ⟨hDCd, hDCc, hdc⟩

end Elements.Book3
