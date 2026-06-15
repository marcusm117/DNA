import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.10: the gnomon KLM and the square CF are equal to twice the rectangle by AB and BC. Chaining
   step7 (gnomon + CF = 2 AF) and step8 (2 AF = 2 (AB·BC)). -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step10 (a b c e n g h f : Point) (AB : Line)
    (hstep7 : ((Triangle.area △ a:c:g + Triangle.area △ a:g:h)
          + (Triangle.area △ g:f:e + Triangle.area △ g:e:n)
          + (Triangle.area △ c:b:f + Triangle.area △ c:f:g))
        + (Triangle.area △ c:b:f + Triangle.area △ c:f:g)
      = (Triangle.area △ a:b:f + Triangle.area △ a:f:h)
        + (Triangle.area △ a:b:f + Triangle.area △ a:f:h))
    (hstep8 : (Triangle.area △ a:b:f + Triangle.area △ a:f:h)
        + (Triangle.area △ a:b:f + Triangle.area △ a:f:h)
      = |(a─b)| * |(b─c)| + |(a─b)| * |(b─c)|) :
    ((Triangle.area △ a:c:g + Triangle.area △ a:g:h)
        + (Triangle.area △ g:f:e + Triangle.area △ g:e:n)
        + (Triangle.area △ c:b:f + Triangle.area △ c:f:g))
      + (Triangle.area △ c:b:f + Triangle.area △ c:f:g)
      = |(a─b)| * |(b─c)| + |(a─b)| * |(b─c)| := by
  rw [hstep7, hstep8]

end Elements.Book2
