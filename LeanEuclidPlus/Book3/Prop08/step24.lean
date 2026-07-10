import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- |KM| = |BM|: both k and b0 are radii, so |m─k| = |m─b0| by assumption, reversed by symmetry.
set_option systemE.solverTime 30 in
theorem helper_3_8_step24
    (m k b0 d : Point)
    (step24_assumption1 : |(m─k)| = |(m─b0)|)
    (step24_assumption2 : |(m─d)| = |(m─d)|) :
    |(k─m)| = |(b0─m)| := by
  linarith [segment_symmetric k m, segment_symmetric b0 m]

end Elements.Book3
