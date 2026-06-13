import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.3.8: rect(AB,BC) = rect(AC,CB) + square(BC). Substitution of steps 4–7:
   step5 (AE = |a─b|*|b─c|) = step4 (AE = AD + CE) = step6 (AD = |a─c|*|c─b|) + step7 (CE = |b─c|²). -/
theorem helper_2_3_step8 (a b c d e f : Point)
    (step4 : Triangle.area △ a:f:e + Triangle.area △ a:e:b =
      (Triangle.area △ a:f:d + Triangle.area △ a:d:c)
    + (Triangle.area △ c:d:e + Triangle.area △ c:e:b))
    (step5 : Triangle.area △ a:f:e + Triangle.area △ a:e:b = |(a─b)| * |(b─c)|)
    (step6 : Triangle.area △ a:f:d + Triangle.area △ a:d:c = |(a─c)| * |(c─b)|)
    (step7 : Triangle.area △ c:d:e + Triangle.area △ c:e:b = |(b─c)| * |(b─c)|) :
    |(a─b)| * |(b─c)| = |(a─c)| * |(c─b)| + |(b─c)| * |(b─c)| := by
  rw [← step5, step4, step6, step7]

end Elements.Book2
