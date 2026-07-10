import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_8_step32
    (ABC : Circle) (k d b0 : Point)
    (habsurd1 : ¬∃ n : Point, n.onCircle ABC ∧ |(d─n)| = |(d─k)| ∧ n ≠ k ∧ n ≠ b0) :
    ¬(∃ n : Point, n.onCircle ABC ∧ |(d─n)| = |(d─k)| ∧ n ≠ k ∧ n ≠ b0) :=
  habsurd1

end Elements.Book3
