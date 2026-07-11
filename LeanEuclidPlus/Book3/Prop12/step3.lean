import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_12_step3 (a f c : Point) (ABC : Circle)
    (left_2 : a.onCircle ABC) (hcABC : c.onCircle ABC)
    (hassump1 : f.isCentre ABC)
    : |(f─a)| = |(f─c)| := by
  euclid_apply (point_on_circle_onlyif f a c ABC)
  euclid_finish

end Elements.Book3
