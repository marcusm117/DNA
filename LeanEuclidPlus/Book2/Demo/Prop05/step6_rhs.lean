import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: the two triangulations of the complement parallelogram HMFG are equal —
   △h:m:f + △h:f:g = △m:h:g + △m:g:f. Direct from parallelogram_area on formParallelogram h m g f. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step6_rhs (h m g f : Point) (KM EF DG BF : Line)
    (hpar : formParallelogram h m g f KM EF DG BF) :
    Triangle.area △ h:m:f + Triangle.area △ h:f:g = Triangle.area △ m:h:g + Triangle.area △ m:g:f := by
  euclid_intros
  euclid_apply (parallelogram_area h m g f KM EF DG BF)
  euclid_finish

end Elements.Book2
