import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.13 sub: the two triangulations of the square DHGN agree —
   △d:h:g + △d:g:n = △h:g:n + △h:n:d. Direct from parallelogram_area on
   formParallelogram h g d n HF DE AD CN. -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step13_dgquad (h g d n : Point) (HF DE AD CN : Line)
    (hpar : formParallelogram h g d n HF DE AD CN) :
    Triangle.area △ d:h:g + Triangle.area △ d:g:n
      = Triangle.area △ h:g:n + Triangle.area △ h:n:d := by
  euclid_intros
  euclid_apply (parallelogram_area h g d n HF DE AD CN)
  euclid_finish

end Elements.Book2
