import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.9: AL = DF. From step8 (CM = AL) and step7 (CM = DF). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step9 (a b c d f g k l m : Point)
    (hstep7 : Triangle.area △ c:b:m + Triangle.area △ c:m:l =
      Triangle.area △ d:b:f + Triangle.area △ d:f:g)
    (hstep8 : Triangle.area △ c:b:m + Triangle.area △ c:m:l =
      Triangle.area △ a:c:l + Triangle.area △ a:l:k) :
    Triangle.area △ a:c:l + Triangle.area △ a:l:k =
      Triangle.area △ d:b:f + Triangle.area △ d:f:g := by
  rw [← hstep8, hstep7]

end Elements.Book2
