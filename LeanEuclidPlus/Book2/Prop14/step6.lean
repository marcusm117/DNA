import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step 6: EF = ED (the Prop 1.3 cut makes |e─f| = |e─d|).
theorem helper_2_14_step6 (e f d : Point) (h : |(e─f)| = |(e─d)|) :
    |(e─f)| = |(e─d)| := h

end Elements.Book2
