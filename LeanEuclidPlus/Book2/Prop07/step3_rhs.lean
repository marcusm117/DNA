import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.3 sub: the two triangulations of the parallelogram GFEN are equal —
   △g:f:e + △g:e:n = △f:g:n + △f:n:e. Direct from parallelogram_area on formParallelogram g f n e. -/
theorem helper_2_7_step3_rhs (g f e n : Point) (HF DE CN BE : Line)
    (hpar : formParallelogram g f n e HF DE CN BE) :
    Triangle.area △ g:f:e + Triangle.area △ g:e:n = Triangle.area △ f:g:n + Triangle.area △ f:n:e := by
  euclid_intros
  euclid_apply (parallelogram_area g f n e HF DE CN BE)
  euclid_finish

end Elements.Book2
