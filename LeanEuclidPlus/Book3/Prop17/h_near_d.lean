import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_17_h_near_d (a e : Point) (BCD : Circle) (AE : Line)
    (hcen : e.isCentre BCD)
    (he : e.onLine AE)
    (hleft : ¬a.insideCircle BCD) (hright : ¬a.onCircle BCD)
    (ha : a.onLine AE) :
    ∃ d : Point, d.onCircle BCD ∧ d.onLine AE ∧ between e d a := by
  have he_in : e.insideCircle BCD := center_inside_circle e BCD hcen
  have ha_out : a.outsideCircle BCD := ⟨hleft, hright⟩
  exact intersection_circle_line_between_points BCD AE e a ⟨he_in, he, ha_out, ha⟩

end Elements.Book3
