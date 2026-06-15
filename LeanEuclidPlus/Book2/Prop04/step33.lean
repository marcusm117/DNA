import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.33: the square on AB equals the squares on AC, CB plus twice the rectangle. Chain:
   |a─b|² = area(ADEB) (step32) = four figures (step31) = |a─c|² + |c─b|² + 2·(|a─c|·|c─b|) (step30). -/
theorem helper_2_4_step33 (a b c d e f g h k : Point)
    (hstep30 : (Triangle.area △ h:g:f + Triangle.area △ h:f:d)
      + (Triangle.area △ c:g:k + Triangle.area △ c:k:b)
      + (Triangle.area △ a:c:g + Triangle.area △ a:g:h)
      + (Triangle.area △ g:k:e + Triangle.area △ g:e:f) =
      |(a─c)| * |(a─c)| + |(c─b)| * |(c─b)| + 2 * (|(a─c)| * |(c─b)|))
    (hstep31 : (Triangle.area △ h:g:f + Triangle.area △ h:f:d)
      + (Triangle.area △ c:g:k + Triangle.area △ c:k:b)
      + (Triangle.area △ a:c:g + Triangle.area △ a:g:h)
      + (Triangle.area △ g:k:e + Triangle.area △ g:e:f) =
      Triangle.area △ a:d:e + Triangle.area △ a:e:b)
    (hstep32 : Triangle.area △ a:d:e + Triangle.area △ a:e:b = |(a─b)| * |(a─b)|) :
    |(a─b)| * |(a─b)| =
      |(a─c)| * |(a─c)| + |(c─b)| * |(c─b)| + 2 * (|(a─c)| * |(c─b)|) := by
  rw [← hstep32, ← hstep31, hstep30]

end Elements.Book2
