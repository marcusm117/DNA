import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_9_step24
  (e f g : Point)
  (hstep15 : |(e─g)| = |(g─f)|) :
  |(e─g)| * |(e─g)| = |(g─f)| * |(g─f)| := by
  rw [hstep15]

end Elements.Book2
