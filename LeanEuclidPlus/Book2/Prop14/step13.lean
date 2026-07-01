import SystemE

namespace Elements.Book2

-- step 13: substitute GF = GH (step12) into step11: BE·EF + GE² = GH².
set_option systemE.solverTime 30 in
theorem helper_2_14_step13 (b₀ e f g h : Point)
    (h_11 : |(b₀─e)| * |(e─f)| + |(e─g)| * |(e─g)| = |(g─f)| * |(g─f)|)
    (h_12 : |(g─f)| = |(g─h)|) :
    |(b₀─e)| * |(e─f)| + |(g─e)| * |(g─e)| = |(g─h)| * |(g─h)| := by
  euclid_finish

end Elements.Book2
