import SystemE

namespace Elements.Book2

-- step 17: the remaining rectangle BE·EF equals the square on EH (|h─e| = |e─h|, from step16).
set_option systemE.solverTime 30 in
theorem helper_2_14_step17 (b₀ e f h : Point)
    (h_16 : |(b₀─e)| * |(e─f)| = |(h─e)| * |(h─e)|) :
    |(b₀─e)| * |(e─f)| = |(e─h)| * |(e─h)| := by
  euclid_finish

end Elements.Book2
