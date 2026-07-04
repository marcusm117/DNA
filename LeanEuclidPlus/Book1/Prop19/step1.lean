import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_19_step1 (h_notgt : ¬|(a─c)| > |(a─b)|) : |(a─c)| = |(a─b)| ∨ |(a─c)| < |(a─b)| := by
  have hle : |(a─c)| ≤ |(a─b)| := le_of_not_gt h_notgt
  exact hle.eq_or_lt

end Elements.Book1
