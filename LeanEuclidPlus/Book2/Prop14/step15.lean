import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step 15: BE·EF + GE² = HE² + EG². Both sides equal GH² (step13 and step14).
theorem helper_2_14_step15 (b₀ e f g h : Point)
    (h_13 : |(b₀─e)| * |(e─f)| + |(g─e)| * |(g─e)| = |(g─h)| * |(g─h)|)
    (h_14 : |(h─e)| * |(h─e)| + |(e─g)| * |(e─g)| = |(g─h)| * |(g─h)|) :
    |(b₀─e)| * |(e─f)| + |(g─e)| * |(g─e)| = |(h─e)| * |(h─e)| + |(e─g)| * |(e─g)| := by
  euclid_finish

end Elements.Book2
