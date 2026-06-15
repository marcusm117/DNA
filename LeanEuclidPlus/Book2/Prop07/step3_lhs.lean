import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.3 sub: the two triangulations of the parallelogram ACGH are equal —
   △a:c:g + △a:g:h = △c:a:h + △c:h:g. Direct from parallelogram_area on formParallelogram a c h g. -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step3_lhs (a c h g : Point) (AB HF AD CN : Line)
    (hpar : formParallelogram a c h g AB HF AD CN) :
    Triangle.area △ a:c:g + Triangle.area △ a:g:h = Triangle.area △ c:a:h + Triangle.area △ c:h:g := by
  euclid_intros
  euclid_apply (parallelogram_area a c h g AB HF AD CN)
  euclid_finish

end Elements.Book2
