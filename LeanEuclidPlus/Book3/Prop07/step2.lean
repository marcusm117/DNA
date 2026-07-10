import SystemE
import Book1.Prop20.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_7_step2 (e b f : Point) (BE BF AD : Line)
    (hassump1 : formTriangle e b f BE BF AD)
    : |(e─b)| + |(e─f)| > |(b─f)| := by
  euclid_apply (Elements.Book1.proposition_20 e b f BE BF AD)
  linarith [segment_symmetric e b, segment_symmetric b f]

end Elements.Book3
