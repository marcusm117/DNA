import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_29_step1
  (hassump1 : ∠ a:g:h ≠ ∠ g:h:d)
  : ∠ a:g:h ≠ ∠ g:h:d → ∠ a:g:h > ∠ g:h:d ∨ ∠ g:h:d > ∠ a:g:h := by
  intro h
  rcases lt_or_gt_of_ne h with h1 | h1
  · exact Or.inr h1
  · exact Or.inl h1

end Elements.Book1
