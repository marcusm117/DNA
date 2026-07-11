import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_14_step8
    (a b c d f g : Point)
    (hstep6 : |(a─b)| = |(a─f)| + |(a─f)|)
    (hstep7 : |(c─d)| = |(c─g)| + |(c─g)|)
    (hassump1 : |(a─b)| = |(c─d)|) :
    |(a─f)| = |(c─g)| := by linarith

end Elements.Book3
