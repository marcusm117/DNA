import SystemE
import Book1.Prop34.variants
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_46_step6
    (a b d e : Point) (AB AD BE DE : Line)
    (step5 : formParallelogram d e a b DE AB AD BE) :
    |(a─b)| = |(d─e)| := by
  euclid_apply (proposition_34' d e a b DE AB AD BE step5)
  euclid_finish

end Elements.Book1
