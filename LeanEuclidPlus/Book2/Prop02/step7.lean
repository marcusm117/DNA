import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.2.7: rect(BA,AC) + rect(AB,BC) = square on AB. Substitution of steps 3–6:
   square AE = |a─b|² (step4) = AF + CE (step3) = |b─a|*|a─c| (step5) + |a─b|*|b─c| (step6). -/
theorem helper_2_2_step7 (a b c d e f : Point)
    (step3 : Triangle.area △ a:d:e + Triangle.area △ a:b:e =
      (Triangle.area △ a:c:f + Triangle.area △ a:d:f)
    + (Triangle.area △ c:b:e + Triangle.area △ c:f:e))
    (step4 : Triangle.area △ a:d:e + Triangle.area △ a:b:e = |(a─b)| * |(a─b)|)
    (step5 : Triangle.area △ a:c:f + Triangle.area △ a:d:f = |(b─a)| * |(a─c)|)
    (step6 : Triangle.area △ c:b:e + Triangle.area △ c:f:e = |(a─b)| * |(b─c)|) :
    |(b─a)| * |(a─c)| + |(a─b)| * |(b─c)| = |(a─b)| * |(a─b)| := by
  rw [← step5, ← step6, ← step3, step4]

end Elements.Book2
