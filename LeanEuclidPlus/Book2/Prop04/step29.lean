import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.29: HF and CK are the squares on AC and CB — restates step24. -/
theorem helper_2_4_step29 (a b c d f g h k : Point)
    (hstep24 : (Triangle.area △ h:g:f + Triangle.area △ h:f:d = |(a─c)| * |(a─c)|) ∧
      (Triangle.area △ c:g:k + Triangle.area △ c:k:b = |(c─b)| * |(c─b)|)) :
    (Triangle.area △ h:g:f + Triangle.area △ h:f:d = |(a─c)| * |(a─c)|) ∧
      (Triangle.area △ c:g:k + Triangle.area △ c:k:b = |(c─b)| * |(c─b)|) := by
  exact hstep24

end Elements.Book2
