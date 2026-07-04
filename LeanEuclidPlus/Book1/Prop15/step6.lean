import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_15_step6
  (c e a d b : Point)
  (h_dec : between d e c)
  (h_aeb : between a e b)
  (hstep5 : ∠ c:e:a + ∠ a:e:d - ∠ a:e:d = ∠ a:e:d + ∠ d:e:b - ∠ a:e:d)
  : ∠ c:e:a = ∠ b:e:d := by
  have h1 : ∠ c:e:a = ∠ d:e:b := by linarith
  have h2 : ∠ d:e:b = ∠ b:e:d := by
    euclid_apply (angle_symm d e b)
    linarith
  linarith

end Elements.Book1
