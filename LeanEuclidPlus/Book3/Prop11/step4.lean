import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step4 (a f g h : Point)
    (h_bet_fgh : between f g h)
    (step3 : |(a─g)| > |(f─h)| - |(g─f)|)
    : |(a─g)| > |(g─h)| := by
  have hbet : |(f─g)| + |(g─h)| = |(f─h)| := between_if f g h h_bet_fgh
  have hfg_sym : |(f─g)| = |(g─f)| := segment_symmetric f g
  linarith

end Elements.Book3
