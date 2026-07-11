import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_17_hAE_int_BCD (e : Point) (BCD : Circle) (AE : Line)
    (he_on : e.onLine AE) (hc : e.isCentre BCD) : AE.intersectsCircle BCD := by
  have he_in : e.insideCircle BCD := center_inside_circle e BCD hc
  exact (intersection_circle_line_2 e BCD AE ⟨he_in, he_on⟩)

end Elements.Book3
