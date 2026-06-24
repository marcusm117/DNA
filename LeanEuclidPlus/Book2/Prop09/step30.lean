import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_9_step30
  (a c e : Point)
  (hstep23 : |(e─a)| * |(e─a)| = 2 * (|(a─c)| * |(a─c)|)) :
  |(e─a)| * |(e─a)| = 2 * (|(a─c)| * |(a─c)|) := hstep23

end Elements.Book2
