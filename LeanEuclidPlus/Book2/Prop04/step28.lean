import SystemE

namespace Elements.Book2

-- 2.4.28: square on AB = squares on AC, CB + twice rectangle(AC,CB).
-- From step27 (four figures = |AB|²) and step26 (four figures = |AC|² + |CB|² + 2·rect).
set_option systemE.solverTime 30 in
theorem helper_2_step28 (a b c d e f g h k : Point)
    (hstep26 : (Triangle.area △ h:g:f + Triangle.area △ h:f:d) +
               (Triangle.area △ c:b:k + Triangle.area △ c:k:g) +
               (Triangle.area △ a:c:g + Triangle.area △ a:g:h) +
               (Triangle.area △ g:k:e + Triangle.area △ g:e:f) =
               |(a─c)| * |(a─c)| + |(c─b)| * |(c─b)| +
                 ((|(a─c)| * |(c─b)|) + (|(a─c)| * |(c─b)|)))
    (hstep27 : (Triangle.area △ h:g:f + Triangle.area △ h:f:d) +
               (Triangle.area △ c:b:k + Triangle.area △ c:k:g) +
               (Triangle.area △ a:c:g + Triangle.area △ a:g:h) +
               (Triangle.area △ g:k:e + Triangle.area △ g:e:f) = |(a─b)| * |(a─b)|) :
    |(a─b)| * |(a─b)| =
    |(a─c)| * |(a─c)| + |(c─b)| * |(c─b)| + 2 * (|(a─c)| * |(c─b)|) := by
  rw [← hstep27, hstep26]; ring

end Elements.Book2
