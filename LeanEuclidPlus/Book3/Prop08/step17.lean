import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- |DK| < |DL|: from step15 (|MK|+|KD| < |ML|+|LD|) and step16 (|MK| = |ML|) by linarith.
set_option systemE.solverTime 30 in
theorem helper_3_8_step17
    (step15 : |(m─k)| + |(k─d)| < |(m─l)| + |(l─d)|)
    (step16 : |(m─k)| = |(m─l)|) :
    |(d─k)| < |(d─l)| := by
  linarith [segment_symmetric k d, segment_symmetric l d]

end Elements.Book3
