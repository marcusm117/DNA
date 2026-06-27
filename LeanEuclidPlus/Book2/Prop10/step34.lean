import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.10.34: restates that the square on EA is double the square on AC (= step27). -/
theorem helper_2_10_step34
  (a c e : Point)
  (hstep27 : |(e─a)| * |(e─a)| = 2 * (|(a─c)| * |(a─c)|)) :
  |(e─a)| * |(e─a)| = 2 * (|(a─c)| * |(a─c)|) := by
  exact hstep27

end Elements.Book2
