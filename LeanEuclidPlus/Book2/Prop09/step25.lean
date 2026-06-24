import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_9_step25
  (e f g : Point)
  (hstep15 : |(e─g)| = |(g─f)|) :
  |(e─g)| * |(e─g)| + |(g─f)| * |(g─f)| = 2 * (|(g─f)| * |(g─f)|) := by
  rw [hstep15]
  ring

end Elements.Book2
