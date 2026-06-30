import SystemE

namespace Elements.Book2

-- step 21: the rectilinear figure A equals the square on EH. From step19 (parallelogram = HE²),
-- step20 (parallelogram = A = △a:b:q + △q:b:c) and |e─h| = |h─e|.
set_option systemE.solverTime 30 in
theorem helper_2_14_step21 (a b c q b₀ e d c₀ h : Point)
    (h_19 : Triangle.area △ b₀:e:d + Triangle.area △ b₀:c₀:d = |(h─e)| * |(h─e)|)
    (h_20 : Triangle.area △ b₀:e:d + Triangle.area △ b₀:c₀:d = Triangle.area △ a:b:q + Triangle.area △ q:b:c) :
    |(e─h)| * |(e─h)| = Triangle.area △ a:b:q + Triangle.area △ q:b:c := by
  euclid_finish

end Elements.Book2
