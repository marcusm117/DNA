import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_7_step27
    (habsurd1 : ¬ (∃ k : Point, k.onCircle ABCD ∧ |(f─k)| = |(f─g)| ∧ k ≠ g ∧ k ≠ h))
    : ¬ (∃ k : Point, k.onCircle ABCD ∧ |(f─k)| = |(f─g)| ∧ k ≠ g ∧ k ≠ h) :=
  habsurd1

end Elements.Book3
