import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_2_step11 (b d f p : Point)
    (hstep9 : |(d─b)| > |(d─p)|)
    (hstep10 : |(d─b)| = |(d─f)|) :
    |(d─f)| > |(d─p)| := by
  linarith

end Elements.Book3
