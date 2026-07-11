import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_17_hane (a e : Point) (BCD : Circle)
    (left : ¬a.insideCircle BCD) (step1 : e.isCentre BCD) : a ≠ e := by
  intro h_eq
  have he_inside : e.insideCircle BCD := center_inside_circle e BCD step1
  exact left (h_eq ▸ he_inside)

end Elements.Book3
