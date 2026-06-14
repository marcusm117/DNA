import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.30: the four figures HF, CK, AG, GE sum to |a─c|² + |c─b|² + 2·(|a─c|·|c─b|). From step29
   (HF = |a─c|², CK = |c─b|²) and step28 (AG + GE = |a─c|·|c─b| + |a─c|·|c─b|). -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step30 (a b c d e f g h k : Point)
    (hstep29 : (Triangle.area △ h:g:f + Triangle.area △ h:f:d = |(a─c)| * |(a─c)|) ∧
      (Triangle.area △ c:g:k + Triangle.area △ c:k:b = |(c─b)| * |(c─b)|))
    (hstep28 : (Triangle.area △ a:c:g + Triangle.area △ a:g:h) +
      (Triangle.area △ g:k:e + Triangle.area △ g:e:f) = |(a─c)| * |(c─b)| + |(a─c)| * |(c─b)|) :
    (Triangle.area △ h:g:f + Triangle.area △ h:f:d)
      + (Triangle.area △ c:g:k + Triangle.area △ c:k:b)
      + (Triangle.area △ a:c:g + Triangle.area △ a:g:h)
      + (Triangle.area △ g:k:e + Triangle.area △ g:e:f) =
      |(a─c)| * |(a─c)| + |(c─b)| * |(c─b)| + 2 * (|(a─c)| * |(c─b)|) := by
  rw [two_mul]
  euclid_finish

end Elements.Book2
