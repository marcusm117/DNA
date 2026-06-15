import SystemE
import Book.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.7.8 sub: |(a─b)| = |(h─f)| and |(a─h)| = |(b─f)|, the opposite-side equalities of the rectangle
   ABFH (formParallelogram a b h f AB HF AD BE) [Prop.~1.34']. -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step8_lens (a b h f : Point) (AB HF AD BE : Line)
    (hpar : formParallelogram a b h f AB HF AD BE) :
    |(a─b)| = |(h─f)| ∧ |(a─h)| = |(b─f)| := by
  euclid_intros
  euclid_apply (proposition_34' a b h f AB HF AD BE)
  euclid_finish

end Elements.Book2
