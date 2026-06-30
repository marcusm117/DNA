import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step 17: the remaining rectangle BE·EF equals the square on EH (|h─e| = |e─h|, from step16).
theorem helper_2_14_step17 (b₀ e f h : Point)
    (h_16 : |(b₀─e)| * |(e─f)| = |(h─e)| * |(h─e)|) :
    |(b₀─e)| * |(e─f)| = |(e─h)| * |(e─h)| := by
  euclid_finish

end Elements.Book2
