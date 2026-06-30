import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_11_step20
    (a f g h b d k : Point)
    (hstep19 : Triangle.area △ f:g:h + Triangle.area △ f:a:h = Triangle.area △ h:b:d + Triangle.area △ h:k:d) :
    Triangle.area △ f:g:h + Triangle.area △ f:a:h = Triangle.area △ h:b:d + Triangle.area △ h:k:d := by
  exact hstep19

end Elements.Book2
