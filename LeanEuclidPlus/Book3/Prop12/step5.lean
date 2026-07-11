import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_12_step5 (a f g c d : Point)
    (step3 : |(f─a)| = |(f─c)|) (step4 : |(g─a)| = |(g─d)|)
    (hassump1 : |(f─a)| = |(f─c)|)
    : |(f─a)| + |(a─g)| = |(f─c)| + |(g─d)| := by
  linarith [segment_symmetric a g]

end Elements.Book3
