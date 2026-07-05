import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_33_step3
  (a b c d : Point)
  (hassump1 : |(a─b)| = |(c─d)|)
  (hassump2 : |(b─c)| = |(b─c)|)
  (step2 : ∠ a:b:c = ∠ b:c:d)
  : (|(a─b)| = |(d─c)| ∧ |(b─c)| = |(c─b)|) ∧ ∠ a:b:c = ∠ b:c:d := by
  exact ⟨⟨by euclid_finish, by euclid_finish⟩, step2⟩

end Elements.Book1
