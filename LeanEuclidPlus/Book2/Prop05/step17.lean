import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.17: gnomon + LG = CB². From step16 (gnomon + LG = AD·DB + CD²) plus the algebraic identity
   AD·DB + CD² = CB²: |a─d| = |a─c| + |c─d| = |c─b| + |c─d| and |c─b| = |c─d| + |d─b|,
   so (|c─b|+|c─d|)(|c─b|-|c─d|) + |c─d|² = |c─b|² − |c─d|² + |c─d|² = |c─b|². nlinarith closes. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step17 (a b c d e f g h l : Point)
    (hac_cb : |(a─c)| = |(c─b)|)
    (hacdb : between a c d) (hcdb : between c d b)
    (hstep16 :
      ((Triangle.area △ d:b:f + Triangle.area △ d:f:g) +
          (Triangle.area △ c:d:h + Triangle.area △ c:h:l)) +
        (Triangle.area △ l:e:g + Triangle.area △ l:g:h) =
        |(a─d)| * |(d─b)| + |(c─d)| * |(c─d)|) :
    ((Triangle.area △ d:b:f + Triangle.area △ d:f:g) +
        (Triangle.area △ c:d:h + Triangle.area △ c:h:l)) +
      (Triangle.area △ l:e:g + Triangle.area △ l:g:h) =
      |(c─b)| * |(c─b)| := by
  have h1 : |(a─d)| = |(a─c)| + |(c─d)| := by euclid_finish
  have h2 : |(c─b)| = |(c─d)| + |(d─b)| := by euclid_finish
  have h_arith : |(a─d)| * |(d─b)| + |(c─d)| * |(c─d)| = |(c─b)| * |(c─b)| := by
    euclid_finish
  exact hstep16.trans h_arith

end Elements.Book2
