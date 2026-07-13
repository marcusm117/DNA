import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step27 (a b c d e : Point)
    (hstep25 : |(d─a)| * |(d─c)| + |(e─c)| * |(e─c)| = |(e─d)| * |(e─d)|)
    (hstep26 : |(e─c)| = |(e─b)|) :
    |(d─a)| * |(d─c)| + |(e─b)| * |(e─b)| = |(e─d)| * |(e─d)| := by
  rw [hstep26] at hstep25; exact hstep25

end Elements.Book3
