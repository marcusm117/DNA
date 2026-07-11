import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_16_step17
    (a d g h : Point)
    (step15 : |(a─d)| > |(d─g)|)
    (step16 : |(d─a)| = |(d─h)|)
    : |(d─h)| > |(d─g)| := by
  linarith [segment_symmetric a d]

end Elements.Book3
