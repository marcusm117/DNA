import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.16: gnomon + LG = |AD|·|DB| + |CD|². From step14 and step15. -/
theorem helper_2_5_step16 (a b c d f g h k l m e : Point)
    (hstep14 : (Triangle.area △ d:b:f + Triangle.area △ d:f:g) +
      (Triangle.area △ c:d:h + Triangle.area △ c:h:l) = |(a─d)| * |(d─b)|)
    (hstep15 : Triangle.area △ l:e:g + Triangle.area △ l:g:h = |(c─d)| * |(c─d)|) :
    ((Triangle.area △ d:b:f + Triangle.area △ d:f:g) +
        (Triangle.area △ c:d:h + Triangle.area △ c:h:l)) +
      (Triangle.area △ l:e:g + Triangle.area △ l:g:h) =
      |(a─d)| * |(d─b)| + |(c─d)| * |(c─d)| := by
  rw [hstep14, hstep15]

end Elements.Book2
