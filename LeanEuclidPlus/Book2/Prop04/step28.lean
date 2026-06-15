import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.28: AG and GE together are twice the rectangle on AC and CB. From step26 (area AG) and
   step27 (area GE), each = |a─c|·|c─b|. -/
theorem helper_2_4_step28 (a b c e f g h k : Point)
    (hstep26 : Triangle.area △ a:c:g + Triangle.area △ a:g:h = |(a─c)| * |(c─b)|)
    (hstep27 : Triangle.area △ g:k:e + Triangle.area △ g:e:f = |(a─c)| * |(c─b)|) :
    (Triangle.area △ a:c:g + Triangle.area △ a:g:h) + (Triangle.area △ g:k:e + Triangle.area △ g:e:f)
      = |(a─c)| * |(c─b)| + |(a─c)| * |(c─b)| := by
  rw [hstep26, hstep27]

end Elements.Book2
