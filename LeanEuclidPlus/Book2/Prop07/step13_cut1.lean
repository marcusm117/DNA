import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.13 sub: cut the whole square ADEB by the vertical CN into left ADNC and right CNEB.
   sum_parallelograms_area on formParallelogram a b d e AB DE AD BE, cut a-c-b (on AB) and d-n-e
   (on DE). -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step13_cut1 (a b c d e n : Point) (AB DE AD BE : Line)
    (hpar : formParallelogram a b d e AB DE AD BE)
    (hacb : between a c b) (hdne : between d n e) :
    Triangle.area △ a:d:n + Triangle.area △ a:n:c
      + (Triangle.area △ c:n:e + Triangle.area △ c:e:b)
      = Triangle.area △ a:d:e + Triangle.area △ a:e:b := by
  euclid_intros
  euclid_apply (sum_parallelograms_area a b d e c n AB DE AD BE)
  euclid_finish

end Elements.Book2
