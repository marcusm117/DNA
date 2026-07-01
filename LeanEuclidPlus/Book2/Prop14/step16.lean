import SystemE

namespace Elements.Book2

-- step 16: "Let the square on GE be taken from both." From step15, BE·EF + GE² = HE² + EG²;
-- since GE² = EG², subtracting gives BE·EF = HE².
set_option systemE.solverTime 30 in
theorem helper_2_14_step16 (b₀ e f g h : Point)
    (h_15 : |(b₀─e)| * |(e─f)| + |(g─e)| * |(g─e)| = |(h─e)| * |(h─e)| + |(e─g)| * |(e─g)|) :
    |(b₀─e)| * |(e─f)| = |(h─e)| * |(h─e)| := by
  euclid_finish

end Elements.Book2
