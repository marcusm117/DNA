import SystemE
import Book.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_46_step15
    (a b d e : Point) (AB AD BE DE : Line) :
    formParallelogram d e a b DE AB AD BE →
      (|(a─b)| = |(d─e)| ∧ |(a─d)| = |(b─e)| ∧ ∠ b:a:d = ∠ b:e:d ∧ ∠ a:d:e = ∠ a:b:e) := by
  intro h
  euclid_apply (proposition_34' d e a b DE AB AD BE h)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> euclid_finish

end Elements.Book1
