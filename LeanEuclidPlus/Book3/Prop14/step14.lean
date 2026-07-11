import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_14_step14
    (e f g : Point)
    (hstep13 : |(f─e)| * |(f─e)| = |(e─g)| * |(e─g)|) :
    |(e─f)| = |(e─g)| := by
  have h1 : |(e─f)| * |(e─f)| = |(e─g)| * |(e─g)| := by
    rw [segment_symmetric e f]; exact hstep13
  have hle1 : |(e─f)| ≤ |(e─g)| := by
    nlinarith [h1, segment_gte_zero (e─f), segment_gte_zero (e─g)]
  have hle2 : |(e─g)| ≤ |(e─f)| := by
    nlinarith [h1, segment_gte_zero (e─f), segment_gte_zero (e─g)]
  linarith

end Elements.Book3
