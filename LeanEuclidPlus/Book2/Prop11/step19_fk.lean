import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_11_step19_fk
    (a c f g h k : Point) (AC GH FG CD : Line)
    (hpar : formParallelogram f c g k AC GH FG CD)
    (hbet_fac : between f a c) (hbet_ghk : between g h k) :
    Triangle.area △ f:g:h + Triangle.area △ f:a:h + Triangle.area △ a:h:k + Triangle.area △ a:k:c
      = Triangle.area △ f:g:k + Triangle.area △ f:c:k := by
  -- cut the rectangle FGKC by the horizontal A-H: FK = (FGHA) + (AHKC).
  euclid_apply (sum_parallelograms_area f c g k a h AC GH FG CD)
  euclid_finish

end Elements.Book2
