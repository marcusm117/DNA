import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_33_step7
  (a b c d : Point) (BC : Line)
  (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
  (h_bd : b ≠ d)
  (step1 : distinctPointsOnLine b c BC)
  (step6 : ∠ b:a:c = ∠ c:d:b ∧ ∠ a:c:b = ∠ d:b:c)
  : ∠ a:c:b = ∠ c:b:d := by
  have h_bc : b ≠ c := step1.right.right
  have hrev : ∠ d:b:c = ∠ c:b:d := by euclid_finish
  exact step6.right.trans hrev

end Elements.Book1
