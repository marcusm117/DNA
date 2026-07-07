import SystemE
import Book.Prop05
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_2_step7_base (a b d : Point) (DA AB DB : Line)
    (htri : formTriangle d a b DA AB DB)
    (hassump1 : |(d─a)| = |(d─b)|) :
    ∠ d:a:b = ∠ d:b:a := by
  euclid_apply (proposition_5' d a b DA AB DB)
  euclid_finish

end Elements.Book3
