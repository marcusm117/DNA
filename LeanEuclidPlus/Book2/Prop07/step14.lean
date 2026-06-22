import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.14: the sum of the squares on AB and BC equals twice the rectangle by AB and BC, plus the
   square on AC. The common quantity "gnomon KLM + CF + DG" equals both AB²+BC² (step13) and
   2(AB·BC)+AC² (step12); equating them (with |c─a| = |a─c| and 2·x = x+x) gives the result. -/
theorem helper_2_7_step14 (a b c d e n g h f : Point)
    (hstep12 : (((Triangle.area △ a:c:g + Triangle.area △ a:g:h) +
        (Triangle.area △ g:f:e + Triangle.area △ g:e:n) +
        (Triangle.area △ c:b:f + Triangle.area △ c:f:g)) +
      (Triangle.area △ c:b:f + Triangle.area △ c:f:g)) +
      (Triangle.area △ d:h:g + Triangle.area △ d:g:n) =
      ((|(a─b)| * |(b─c)|) + (|(a─b)| * |(b─c)|)) + |(a─c)| * |(a─c)|)
    (hstep13 : (((Triangle.area △ a:c:g + Triangle.area △ a:g:h) +
        (Triangle.area △ g:f:e + Triangle.area △ g:e:n) +
        (Triangle.area △ c:b:f + Triangle.area △ c:f:g)) +
      (Triangle.area △ c:b:f + Triangle.area △ c:f:g)) +
      (Triangle.area △ d:h:g + Triangle.area △ d:g:n) =
      |(a─b)| * |(a─b)| + |(b─c)| * |(b─c)|) :
    |(a─b)| * |(a─b)| + |(b─c)| * |(b─c)| =
      2 * (|(a─b)| * |(b─c)|) + |(c─a)| * |(c─a)| := by
  rw [two_mul]
  euclid_finish

end Elements.Book2
