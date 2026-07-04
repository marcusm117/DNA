import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_15_h1
  (a e c d b : Point)
  (h_dec : between d e c)
  (h_aeb : between a e b)
  (hstep6 : ∠ c:e:a = ∠ b:e:d)
  : ∠ a:e:c = ∠ d:e:b := by
  have h1 : ∠ c:e:a = ∠ a:e:c := by
    euclid_apply (angle_symm c e a)
    linarith
  have h2 : ∠ b:e:d = ∠ d:e:b := by
    euclid_apply (angle_symm b e d)
    linarith
  linarith

end Elements.Book1
