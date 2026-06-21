import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7 sub: the two triangulations of the complement parallelogram HMFG are equal —
   △h:m:f + △h:f:g = △m:h:g + △m:g:f. Direct from parallelogram_area on formParallelogram h m g f. -/
theorem helper_2_6_step7_rhs (h m g f : Point) (KM EF BG DF : Line)
    (hpar : formParallelogram h m g f KM EF BG DF) :
    Triangle.area △ h:m:f + Triangle.area △ h:f:g = Triangle.area △ m:h:g + Triangle.area △ m:g:f := by
  euclid_intros
  euclid_apply (parallelogram_area h m g f KM EF BG DF)
  euclid_finish

end Elements.Book2
