import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.11 sub: d ≠ h. Between d h g → d ≠ h (betweenness endpoints are distinct). -/
theorem helper_2_5_step11_ahpar_dh (d h g : Point)
    (hdhg : between d h g) :
    d ≠ h := by
  euclid_intros
  euclid_finish

end Elements.Book2
