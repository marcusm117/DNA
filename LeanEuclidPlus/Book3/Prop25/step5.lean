import SystemE

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step5 (a b d : Point)
    (hgt : ∠ a:b:d > ∠ b:a:d) :
    ∠ a:b:d > ∠ b:a:d := by
  exact hgt

end Elements.Book3
