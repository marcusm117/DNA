import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.25 sub: the two triangulations of the parallelogram GKEF are equal —
   △g:k:e + △g:e:f = △k:g:f + △k:f:e. Direct from parallelogram_area on formParallelogram g k e f. -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step25_rhs (g k e f : Point) (HK DE CF BE : Line)
    (hpar : formParallelogram g k f e HK DE CF BE) :
    Triangle.area △ g:k:e + Triangle.area △ g:e:f = Triangle.area △ k:g:f + Triangle.area △ k:f:e := by
  euclid_intros
  euclid_apply (parallelogram_area g k f e HK DE CF BE)
  euclid_finish

end Elements.Book2
