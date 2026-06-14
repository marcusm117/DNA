import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.32 sub: the two triangulations of the parallelogram ADEB are equal —
   △a:d:e + △a:e:b = △b:a:d + △b:e:d. Direct from parallelogram_area on formParallelogram b e a d. -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step32_bridge (a b d e : Point) (BE AD AB DE : Line)
    (hpar : formParallelogram b e a d BE AD AB DE) :
    Triangle.area △ a:d:e + Triangle.area △ a:e:b = Triangle.area △ b:a:d + Triangle.area △ b:e:d := by
  euclid_intros
  euclid_apply (parallelogram_area b e a d BE AD AB DE)
  euclid_finish

end Elements.Book2
