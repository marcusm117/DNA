import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- sub-fact for 2.3.6: the left-rectangle area identity △a:f:d + △a:d:c = |a─c|*|a─f|. Given the
   parallelogram a c f d (step6_par), rectangle_area fires; its right-angle precondition ∠a:f:d
   follows from ∠c:d:e = ∟ and the parallel verticals. -/
theorem helper_2_3_step6_area (a c d e f : Point) (AB DE CD AF : Line)
    (hpar : formParallelogram a c f d AB DE AF CD)
    (hedf : between e d f) (hcde : ∠ c:d:e = ∟)
    (heDE : e.onLine DE) :
    Triangle.area △ a:f:d + Triangle.area △ a:d:c = |(a─c)| * |(a─f)| := by
  euclid_intros
  have hafd : ∠ a:f:d = ∟ := by euclid_finish
  euclid_apply (rectangle_area a c f d AB DE AF CD)
  euclid_finish

end Elements.Book2
