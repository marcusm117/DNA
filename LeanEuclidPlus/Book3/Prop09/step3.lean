import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_9_step3
    (a b d e : Point)
    (hassump1 : |(a─e)| = |(e─b)|)
    (hassump2 : |(e─d)| = |(e─d)|)
    : |(a─e)| = |(b─e)| ∧ |(e─d)| = |(e─d)| := by
  exact ⟨hassump1.trans (segment_symmetric b e).symm, rfl⟩

end Elements.Book3
