import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
/- sub-fact for 2.2.6: the right-rectangle area identity △c:b:e + △c:f:e = |b─c|*|b─e|. Given the
   parallelogram b c e f (step6_par) and the right angle ∠b:e:f (step6_bef), rectangle_area fires. -/
theorem helper_2_2_step6_area (b c e f : Point) (AB DE BE CF : Line)
    (hpar : formParallelogram b c e f AB DE BE CF)
    (hbef : ∠ b:e:f = ∟) :
    Triangle.area △ c:b:e + Triangle.area △ c:f:e = |(b─c)| * |(b─e)| := by
  euclid_apply (rectangle_area b c e f AB DE BE CF)
  euclid_finish

end Elements.Book2
