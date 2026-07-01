import SystemE

namespace Elements.Book2

-- step 20: BD equals the rectilinear figure A — this is step1's area equality (the parallelogram BD
-- was constructed equal to the quadrilateral A = △a:b:q + △q:b:c).
set_option systemE.solverTime 30 in
theorem helper_2_14_step20 (a b c q b₀ e d c₀ : Point)
    (h_area : Triangle.area △ b₀:e:d + Triangle.area △ b₀:c₀:d = Triangle.area △ a:b:q + Triangle.area △ q:b:c) :
    Triangle.area △ b₀:e:d + Triangle.area △ b₀:c₀:d = Triangle.area △ a:b:q + Triangle.area △ q:b:c := h_area

end Elements.Book2
