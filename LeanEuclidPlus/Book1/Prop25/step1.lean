import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_25_step1 (h_notgt : ¬∠ b:a:c > ∠ e:d:f) : ∠ b:a:c = ∠ e:d:f ∨ ∠ b:a:c < ∠ e:d:f := by
  have hle : ∠ b:a:c ≤ ∠ e:d:f := le_of_not_gt h_notgt
  exact hle.eq_or_lt

end Elements.Book1
