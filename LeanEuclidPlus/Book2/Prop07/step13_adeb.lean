import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.13 sub: area(ADEB) = |a─b|². ADEB = formParallelogram a b d e AB DE AD BE with the right angle
   ∠a:d:e = ∟ (vertex d in the c-slot); rectangle_area gives △a:d:e + △a:b:e = |a─b|·|a─d|, and
   |a─d| = |a─b| (square side), so the area (= △a:d:e + △a:e:b) is |a─b|·|a─b|. -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step13_adeb (a b d e : Point) (AB DE AD BE : Line)
    (hpar : formParallelogram a b d e AB DE AD BE)
    (hade : ∠ a:d:e = ∟) (hadab : |(a─d)| = |(a─b)|) :
    Triangle.area △ a:d:e + Triangle.area △ a:e:b = |(a─b)| * |(a─b)| := by
  euclid_intros
  euclid_apply (rectangle_area a b d e AB DE AD BE)
  euclid_finish

end Elements.Book2
