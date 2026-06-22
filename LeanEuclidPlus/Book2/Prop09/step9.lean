import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
-- step9 (2.9.9): "And they are equal." — restates step7.
theorem helper_2_9_step9
  (a c e : Point)
  (h7 : ∠ e:a:c = ∠ a:e:c) : ∠ e:a:c = ∠ a:e:c := by
  euclid_finish

end Elements.Book2
