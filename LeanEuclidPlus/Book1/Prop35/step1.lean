import SystemE
import Book1.Prop34.variants
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_35_step1
  (a d b c : Point) (AF BC AB CD : Line)
  (hassump1 : formParallelogram a d b c AF BC AB CD)
  : |(a─d)| = |(b─c)| := by
  euclid_apply (proposition_34' a d b c AF BC AB CD)
  euclid_finish

end Elements.Book1
