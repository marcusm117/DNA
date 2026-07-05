import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step1 (a b d e : Point)
    (hne : |(a─b)| ≠ |(d─e)|) :
    |(a─b)| > |(d─e)| ∨ |(d─e)| > |(a─b)| := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact Or.inr h
  · exact Or.inl h

end Elements.Book1
