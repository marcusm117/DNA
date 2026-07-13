import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_35_step1 (a b c d e : Point)
  (hassump1 : |(a─e)| = |(e─c)| ∧ |(e─c)| = |(d─e)| ∧ |(d─e)| = |(b─e)|)
  : |(a─e)| * |(e─c)| = |(b─e)| * |(e─d)| := by
  euclid_finish

end Elements.Book3
