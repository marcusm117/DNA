import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_15_h2
  (c e b d a : Point)
  (h_dec : between d e c)
  (h_aeb : between a e b)
  (hstep7 : ∠ c:e:b = ∠ d:e:a)
  : ∠ c:e:b = ∠ a:e:d := by
  have h : ∠ d:e:a = ∠ a:e:d := by
    euclid_apply (angle_symm d e a)
    linarith
  linarith

end Elements.Book1
