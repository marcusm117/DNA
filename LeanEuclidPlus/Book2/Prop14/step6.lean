import SystemE

namespace Elements.Book2

-- step 6: EF = ED (the Prop 1.3 cut makes |e─f| = |e─d|).
set_option systemE.solverTime 30 in
theorem helper_2_14_step6 (e f d : Point) (h : |(e─f)| = |(e─d)|) :
    |(e─f)| = |(e─d)| := h

end Elements.Book2
