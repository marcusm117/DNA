import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.7: CM = DF. Add DM to both sides of step6 (CH = HF). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step7 (c d f g h l m b : Point)
    (hstep6 : Triangle.area △ c:d:h + Triangle.area △ c:h:l =
      Triangle.area △ h:m:f + Triangle.area △ h:f:g) :
    Triangle.area △ c:b:m + Triangle.area △ c:m:l =
      Triangle.area △ d:b:f + Triangle.area △ d:f:g := by
  euclid_finish

end Elements.Book2