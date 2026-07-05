import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_25_step11
    (h_ne : ∠ b:a:c ≠ ∠ e:d:f)
    (h_nlt : ¬(∠ b:a:c < ∠ e:d:f)) :
    ∠ b:a:c > ∠ e:d:f := by
  rcases lt_or_gt_of_ne h_ne with h | h
  · exact absurd h h_nlt
  · exact h

end Elements.Book1
