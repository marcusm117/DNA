import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_14_step24
    (a c f g : Point)
    (hstep23 : |(a─f)| * |(a─f)| = |(c─g)| * |(c─g)|) :
    |(a─f)| = |(c─g)| := by
  have hle1 : |(a─f)| ≤ |(c─g)| := by
    nlinarith [hstep23, segment_gte_zero (a─f), segment_gte_zero (c─g)]
  have hle2 : |(c─g)| ≤ |(a─f)| := by
    nlinarith [hstep23, segment_gte_zero (a─f), segment_gte_zero (c─g)]
  linarith

end Elements.Book3
