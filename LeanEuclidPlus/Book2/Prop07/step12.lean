import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.12: the gnomon KLM and the squares BG (= CF) and GD (= DG) are equal to twice the rectangle
   by AB and BC, plus the square on AC. Adding step11 (DG = |a─c|²) to both sides of step10
   (gnomon + CF = 2 (AB·BC)). -/
theorem helper_2_7_step12 (a b c d e n g h f : Point)
    (hstep10 : ((Triangle.area △ a:c:g + Triangle.area △ a:g:h)
          + (Triangle.area △ g:f:e + Triangle.area △ g:e:n)
          + (Triangle.area △ c:b:f + Triangle.area △ c:f:g))
        + (Triangle.area △ c:b:f + Triangle.area △ c:f:g)
      = |(a─b)| * |(b─c)| + |(a─b)| * |(b─c)|)
    (hstep11 : Triangle.area △ d:h:g + Triangle.area △ d:g:n = |(a─c)| * |(a─c)|) :
    (((Triangle.area △ a:c:g + Triangle.area △ a:g:h)
          + (Triangle.area △ g:f:e + Triangle.area △ g:e:n)
          + (Triangle.area △ c:b:f + Triangle.area △ c:f:g))
        + (Triangle.area △ c:b:f + Triangle.area △ c:f:g))
      + (Triangle.area △ d:h:g + Triangle.area △ d:g:n)
      = (|(a─b)| * |(b─c)| + |(a─b)| * |(b─c)|) + |(a─c)| * |(a─c)| := by
  rw [hstep10, hstep11]

end Elements.Book2
