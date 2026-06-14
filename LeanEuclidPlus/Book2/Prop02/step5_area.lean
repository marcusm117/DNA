import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
/- sub-fact for 2.2.5: the left-rectangle area identity △a:d:f + △a:c:f = |a─c|*|a─d|. Given the
   parallelogram a c d f (step5_par), rectangle_area fires; its right-angle precondition ∠a:d:f
   follows from ∠a:d:e = ∟ and the parallel verticals. -/
theorem helper_2_2_step5_area (a c d f : Point) (AB DE AD CF : Line)
    (hpar : formParallelogram a c d f AB DE AD CF)
    (hadf : ∠ a:d:f = ∟) :
    Triangle.area △ a:d:f + Triangle.area △ a:c:f = |(a─c)| * |(a─d)| := by
  euclid_apply (rectangle_area a c d f AB DE AD CF)
  euclid_finish

end Elements.Book2
