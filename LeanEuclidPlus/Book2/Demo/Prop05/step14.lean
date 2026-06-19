import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.14: gnomon NOP = |AD|·|DB|. From step11 (AH = gnomon) and step12 (AH = |AD|·|DB|). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step14 (a b c d f g h k l m : Point)
    (hstep11 : Triangle.area △ a:d:h + Triangle.area △ a:h:k =
      (Triangle.area △ d:b:f + Triangle.area △ d:f:g) +
      (Triangle.area △ c:d:h + Triangle.area △ c:h:l))
    (hstep12 : Triangle.area △ a:d:h + Triangle.area △ a:h:k = |(a─d)| * |(d─b)|) :
    (Triangle.area △ d:b:f + Triangle.area △ d:f:g) +
      (Triangle.area △ c:d:h + Triangle.area △ c:h:l) = |(a─d)| * |(d─b)| := by
  rw [← hstep11, hstep12]

end Elements.Book2
