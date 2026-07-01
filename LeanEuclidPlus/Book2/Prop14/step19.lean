import SystemE

namespace Elements.Book2

-- step 19: the parallelogram BD equals the square on HE. From step18 (area = BE·EF) and step16
-- (BE·EF = HE²).
set_option systemE.solverTime 30 in
theorem helper_2_14_step19 (b₀ e d c₀ f h : Point)
    (h_18 : (△ b₀:e:d).area + (△ b₀:c₀:d).area = |(b₀─e)| * |(e─f)|)
    (h_16 : |(b₀─e)| * |(e─f)| = |(h─e)| * |(h─e)|) :
    (△ b₀:e:d).area + (△ b₀:c₀:d).area = |(h─e)| * |(h─e)| := by
  euclid_finish

end Elements.Book2
