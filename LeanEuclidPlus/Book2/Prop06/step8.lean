import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.8: (rectangle) AL = HF. From step6 (AL = CH) and step7 (CH = HF), by transitivity. Pure
   area-arithmetic over the two prior step equalities. -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step8 (a c l k b h m f g : Point)
    (hstep6 : Triangle.area △ a:c:l + Triangle.area △ a:l:k =
      Triangle.area △ c:b:h + Triangle.area △ c:h:l)
    (hstep7 : Triangle.area △ c:b:h + Triangle.area △ c:h:l =
      Triangle.area △ h:m:f + Triangle.area △ h:f:g) :
    Triangle.area △ a:c:l + Triangle.area △ a:l:k =
      Triangle.area △ h:m:f + Triangle.area △ h:f:g := by
  euclid_finish

end Elements.Book2
