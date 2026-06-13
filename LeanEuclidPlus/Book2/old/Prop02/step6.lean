import SystemE

namespace Elements.Book2

/- 2.2.6: rect(BA,AC) + rect(AB,BC) = square on AB. Substitution of steps 2–5. -/
set_option systemE.solverTime 30 in
theorem helper_2_2_step6 (a b c d e f : Point)
    (step2 : Triangle.area △ d:a:b + Triangle.area △ d:b:e =
             (Triangle.area △ d:a:c + Triangle.area △ d:c:f)
           + (Triangle.area △ f:c:b + Triangle.area △ f:b:e))
    (step3 : Triangle.area △ d:a:b + Triangle.area △ d:b:e = |(a─b)| * |(a─b)|)
    (step4 : Triangle.area △ d:a:c + Triangle.area △ d:c:f = |(b─a)| * |(a─c)|)
    (step5 : Triangle.area △ f:c:b + Triangle.area △ f:b:e = |(a─b)| * |(b─c)|) :
    |(b─a)| * |(a─c)| + |(a─b)| * |(b─c)| = |(a─b)| * |(a─b)| := by
  rw [← step3, step2, step4, step5]

end Elements.Book2
