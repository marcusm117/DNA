import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.5: AF + CE is double AF. Immediate from step4 (AF = CE): substituting CE = AF gives
   AF + CE = AF + AF. -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step5 (a b c e n g h f : Point)
    (hstep4 : Triangle.area △ a:b:f + Triangle.area △ a:f:h
      = Triangle.area △ c:b:e + Triangle.area △ c:e:n) :
    (Triangle.area △ a:b:f + Triangle.area △ a:f:h) + (Triangle.area △ c:b:e + Triangle.area △ c:e:n)
      = (Triangle.area △ a:b:f + Triangle.area △ a:f:h) + (Triangle.area △ a:b:f + Triangle.area △ a:f:h) := by
  rw [hstep4]

end Elements.Book2
