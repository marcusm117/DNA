import SystemE

namespace Elements.Book2

-- 2.4.23: GE = rectangle(AC,CB). From step21 (area AG = area GE) and step22 (area AG = |AC|·|CB|).
set_option systemE.solverTime 30 in
theorem helper_2_step23 (a b c e f g h k : Point)
    (hstep21 : Triangle.area △ a:c:g + Triangle.area △ a:g:h =
               Triangle.area △ g:k:e + Triangle.area △ g:e:f)
    (hstep22 : Triangle.area △ a:c:g + Triangle.area △ a:g:h = |(a─c)| * |(c─b)|) :
    Triangle.area △ g:k:e + Triangle.area △ g:e:f = |(a─c)| * |(c─b)| := by
  euclid_intros
  euclid_finish

end Elements.Book2
