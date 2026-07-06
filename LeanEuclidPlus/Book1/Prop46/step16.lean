import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_46_step16
    (a b d e : Point) (AB AD BE DE : Line)
    (step5 : formParallelogram d e a b DE AB AD BE)
    (step13 : ∠ b:a:d = ∟)
    (step14 : ∠ a:d:e = ∟)
    (step15 : formParallelogram d e a b DE AB AD BE →
      (|(a─b)| = |(d─e)| ∧ |(a─d)| = |(b─e)| ∧ ∠ b:a:d = ∠ b:e:d ∧ ∠ a:d:e = ∠ a:b:e)) :
    ∠ a:b:e = ∟ ∧ ∠ b:e:d = ∟ := by
  have h34 := step15 step5
  exact ⟨by linarith [h34.2.2.2, step14], by linarith [h34.2.2.1, step13]⟩

end Elements.Book1
