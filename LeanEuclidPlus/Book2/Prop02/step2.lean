import SystemE

namespace Elements.Book2

/- 2.2.2: square AE = rectangles AF + CE. Area split of the square by C (on AB) and F (on DE). -/
set_option systemE.solverTime 30 in
theorem helper_2_2_step2 (a b c d e f : Point) (AB DE AD BE : Line)
    (hsq : formParallelogram d e a b DE AB AD BE)
    (hdfe : between d f e) (hacb : between a c b) :
    Triangle.area △ d:a:b + Triangle.area △ d:b:e =
      (Triangle.area △ d:a:c + Triangle.area △ d:c:f)
    + (Triangle.area △ f:c:b + Triangle.area △ f:b:e) := by
  euclid_intros
  euclid_apply (sum_parallelograms_area d e a b f c DE AB AD BE)
  euclid_finish

end Elements.Book2
