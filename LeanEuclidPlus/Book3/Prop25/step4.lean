import SystemE

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step4 (a b d : Point) :
    ∠ a:b:d > ∠ b:a:d ∨ ∠ a:b:d = ∠ b:a:d ∨ ∠ a:b:d < ∠ b:a:d := by
  euclid_finish

end Elements.Book3
