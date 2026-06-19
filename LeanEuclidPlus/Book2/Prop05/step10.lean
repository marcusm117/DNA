import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.10: Add CH to both sides of AL = DF. -/
theorem helper_2_5_step10 (a b c d f g h k l m : Point)
    (hstep9 : Triangle.area △ a:c:l + Triangle.area △ a:l:k =
      Triangle.area △ d:b:f + Triangle.area △ d:f:g) :
    (Triangle.area △ a:c:l + Triangle.area △ a:l:k) +
        (Triangle.area △ c:d:h + Triangle.area △ c:h:l) =
      (Triangle.area △ d:b:f + Triangle.area △ d:f:g) +
        (Triangle.area △ c:d:h + Triangle.area △ c:h:l) := by
  rw [hstep9]

end Elements.Book2
