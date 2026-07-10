import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_7_step3 (a e f d : Point) (AD : Line)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hbet_aed : between a e d) (hbet_efd : between e f d)
    (hassump1 : |(a─e)| = |(e─b)|)
    : |(e─b)| + |(e─f)| = |(f─a)| := by
  -- between a e d + between e f d → between a e f
  have hbet_aef : between a e f := by euclid_finish
  -- between a e f → |a─f| = |a─e| + |e─f|
  have haf : |(a─e)| + |(e─f)| = |(a─f)| := between_if a e f hbet_aef
  linarith [segment_symmetric a e, segment_symmetric a f, segment_symmetric f a]

end Elements.Book3
