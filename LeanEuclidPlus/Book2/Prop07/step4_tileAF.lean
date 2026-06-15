import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.4 sub: the top-half rectangle AF (= ABFH) is tiled by the vertical CN into AG (ACGH) and
   CF (CBFG). sum_parallelograms_area on formParallelogram a b h f AB HF AD BE, cut at c (between
   a c b on AB) and g (between h g f on HF), gives the four-triangle sum equal to the two halves. -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step4_tileAF (a b c h g f : Point) (AB HF AD BE : Line)
    (hpar : formParallelogram a b h f AB HF AD BE)
    (hacb : between a c b) (hhgf : between h g f) :
    Triangle.area △ a:c:g + Triangle.area △ a:g:h + (Triangle.area △ c:b:f + Triangle.area △ c:f:g)
      = Triangle.area △ a:b:f + Triangle.area △ a:f:h := by
  euclid_intros
  euclid_apply (sum_parallelograms_area a b h f c g AB HF AD BE)
  euclid_finish

end Elements.Book2
