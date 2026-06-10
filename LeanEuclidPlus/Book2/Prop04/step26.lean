import SystemE

namespace Elements.Book2

-- 2.4.26: HF + CK + AG + GE = |AC|² + |CB|² + 2·rect(AC,CB).
-- From step25 (area HF = |AC|², area CK = |CB|²) and step24 (area AG + area GE = 2·|AC|·|CB|).
set_option systemE.solverTime 30 in
theorem helper_2_step26 (a b c d e f g h k : Point)
    (hstep25 : (Triangle.area △ h:g:f + Triangle.area △ h:f:d = |(a─c)| * |(a─c)|) ∧
               (Triangle.area △ c:b:k + Triangle.area △ c:k:g = |(c─b)| * |(c─b)|))
    (hstep24 : (Triangle.area △ a:c:g + Triangle.area △ a:g:h) +
               (Triangle.area △ g:k:e + Triangle.area △ g:e:f) = 2 * (|(a─c)| * |(c─b)|)) :
    (Triangle.area △ h:g:f + Triangle.area △ h:f:d) +
    (Triangle.area △ c:b:k + Triangle.area △ c:k:g) +
    (Triangle.area △ a:c:g + Triangle.area △ a:g:h) +
    (Triangle.area △ g:k:e + Triangle.area △ g:e:f) =
    |(a─c)| * |(a─c)| + |(c─b)| * |(c─b)| + 2 * (|(a─c)| * |(c─b)|) := by
  obtain ⟨hHF, hCK⟩ := hstep25
  rw [hHF, hCK]; rw [← hstep24]; ring

end Elements.Book2
