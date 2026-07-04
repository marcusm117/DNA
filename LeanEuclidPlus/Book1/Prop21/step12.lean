import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_21_step12 (a b c d e : Point)
    (hstep10 : ∠ c:e:b > ∠ b:a:c)
    (hstep11 : ∠ b:d:c > ∠ c:e:b) :
    ∠ b:d:c > ∠ b:a:c := by
  linarith

end Elements.Book1
