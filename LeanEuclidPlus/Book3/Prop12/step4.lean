import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_12_step4 (a g d : Point) (ADE : Circle)
    (left_3 : a.onCircle ADE) (hdADE : d.onCircle ADE)
    (hassump1 : g.isCentre ADE)
    : |(g─a)| = |(g─d)| := by
  euclid_apply (point_on_circle_onlyif g a d ADE)
  euclid_finish

end Elements.Book3
