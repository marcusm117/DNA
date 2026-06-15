import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.4 sub: the right-half rectangle CE (= CBEN) is tiled by the horizontal HF into CF (CBFG) and
   GE (GFEN). sum_parallelograms_area on formParallelogram c n b e CN BE AB DE, cut at g (between
   c g n on CN) and f (between b f e on BE), gives the four-triangle sum equal to the two halves. -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step4_tileCE (c n b e g f : Point) (CN BE AB DE : Line)
    (hpar : formParallelogram c n b e CN BE AB DE)
    (hcgn : between c g n) (hbfe : between b f e) :
    (Triangle.area △ c:b:f + Triangle.area △ c:f:g) + (Triangle.area △ g:f:e + Triangle.area △ g:e:n)
      = Triangle.area △ c:b:e + Triangle.area △ c:e:n := by
  euclid_intros
  euclid_apply (sum_parallelograms_area c n b e g f CN BE AB DE)
  euclid_finish

end Elements.Book2
