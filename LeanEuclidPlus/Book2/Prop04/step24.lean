import SystemE

namespace Elements.Book2

-- 2.4.24: AG and GE together = twice rectangle(AC,CB). From step22 + step23.
set_option systemE.solverTime 30 in
theorem helper_2_step24 (a b c e f g h k : Point)
    (hstep22 : Triangle.area △ a:c:g + Triangle.area △ a:g:h = |(a─c)| * |(c─b)|)
    (hstep23 : Triangle.area △ g:k:e + Triangle.area △ g:e:f = |(a─c)| * |(c─b)|) :
    (Triangle.area △ a:c:g + Triangle.area △ a:g:h) +
    (Triangle.area △ g:k:e + Triangle.area △ g:e:f) =
    (|(a─c)| * |(c─b)|) + (|(a─c)| * |(c─b)|) := by
  rw [hstep22, hstep23]

end Elements.Book2
