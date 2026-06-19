import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.18: |AD|·|DB| + |CD|² = |CB|². From step16 and step17. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step18 (a b c d e f g h k l m : Point)
    (hstep16 : ((Triangle.area △ d:b:f + Triangle.area △ d:f:g) +
        (Triangle.area △ c:d:h + Triangle.area △ c:h:l)) +
      (Triangle.area △ l:e:g + Triangle.area △ l:g:h) =
      |(a─d)| * |(d─b)| + |(c─d)| * |(c─d)|)
    (hstep17 : ((Triangle.area △ d:b:f + Triangle.area △ d:f:g) +
        (Triangle.area △ c:d:h + Triangle.area △ c:h:l)) +
      (Triangle.area △ l:e:g + Triangle.area △ l:g:h) =
      |(c─b)| * |(c─b)|) :
    |(a─d)| * |(d─b)| + |(c─d)| * |(c─d)| = |(c─b)| * |(c─b)| := by
  rw [← hstep16, hstep17]

end Elements.Book2
