import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step24
    (hne2 : |(b─c)| ≠ |(e─f)|) :
    |(b─c)| > |(e─f)| ∨ |(e─f)| > |(b─c)| := by
  rcases lt_or_gt_of_ne hne2 with h | h
  · exact Or.inr h
  · exact Or.inl h

end Elements.Book1
