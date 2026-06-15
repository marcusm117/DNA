import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.27: GE is also the rectangle on AC and CB — area(GE) = |a─c|·|c─b|. From area(AG) = area(GE)
   (step25) and area(AG) = |a─c|·|c─b| (step26). -/
theorem helper_2_4_step27 (a b c e f g h k : Point)
    (hstep25 : Triangle.area △ a:c:g + Triangle.area △ a:g:h
      = Triangle.area △ g:k:e + Triangle.area △ g:e:f)
    (hstep26 : Triangle.area △ a:c:g + Triangle.area △ a:g:h = |(a─c)| * |(c─b)|) :
    Triangle.area △ g:k:e + Triangle.area △ g:e:f = |(a─c)| * |(c─b)| := by
  rw [← hstep25, hstep26]

end Elements.Book2
