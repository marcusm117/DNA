import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: the two triangulations of the complement parallelogram CDHL are equal —
   △c:d:h + △c:h:l = △d:c:l + △d:l:h. Direct from parallelogram_area on formParallelogram c d l h. -/
theorem helper_2_5_step6_lhs (c d l h : Point) (AB KM CE DG : Line)
    (hpar : formParallelogram c d l h AB KM CE DG) :
    Triangle.area △ c:d:h + Triangle.area △ c:h:l = Triangle.area △ d:c:l + Triangle.area △ d:l:h := by
  euclid_intros
  euclid_apply (parallelogram_area c d l h AB KM CE DG)
  euclid_finish

end Elements.Book2
