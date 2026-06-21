import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.10: whole AM = gnomon NOP. Substitute step8 (AL = HF) into step9 (AM = AL + CM): AM = HF + CM,
   i.e. AM = (c:d:m + c:m:l) + (h:m:f + h:f:g). Pure area-arithmetic over the two prior equalities. -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step10 (a c d h m f g l k : Point)
    (step8 : Triangle.area △ a:c:l + Triangle.area △ a:l:k =
      Triangle.area △ h:m:f + Triangle.area △ h:f:g)
    (step9 : Triangle.area △ a:d:m + Triangle.area △ a:m:k =
      (Triangle.area △ a:c:l + Triangle.area △ a:l:k) +
      (Triangle.area △ c:d:m + Triangle.area △ c:m:l)) :
    Triangle.area △ a:d:m + Triangle.area △ a:m:k =
      (Triangle.area △ c:d:m + Triangle.area △ c:m:l) +
      (Triangle.area △ h:m:f + Triangle.area △ h:f:g) := by
  euclid_finish

end Elements.Book2
