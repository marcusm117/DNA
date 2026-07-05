import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_24_step2
  (d g a c : Point)
  (h_dg_ac : |(d─g)| = |(a─c)|)
  : |(d─g)| = |(a─c)| ∨ |(d─g)| = |(d─f)| := Or.inl h_dg_ac

end Elements.Book1
