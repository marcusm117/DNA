import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7 sub: the two triangulations of the complement parallelogram CBHL are equal —
   △c:b:h + △c:h:l = △b:c:l + △b:l:h. Direct from parallelogram_area on formParallelogram c b l h. -/
theorem helper_2_6_step7_lhs (c b l h : Point) (AB KM CE BG : Line)
    (hpar : formParallelogram c b l h AB KM CE BG) :
    Triangle.area △ c:b:h + Triangle.area △ c:h:l = Triangle.area △ b:c:l + Triangle.area △ b:l:h := by
  euclid_intros
  euclid_apply (parallelogram_area c b l h AB KM CE BG)
  euclid_finish

end Elements.Book2
