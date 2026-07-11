import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_17_step9 (a b d e f : Point)
    (hstep7 : |(e─a)| = |(e─f)|)
    (hstep8 : |(e─d)| = |(e─b)|) :
    |(a─e)| = |(f─e)| ∧ |(e─b)| = |(e─d)| := by
  exact ⟨by linarith [segment_symmetric e a, segment_symmetric e f],
         by linarith⟩

end Elements.Book3
