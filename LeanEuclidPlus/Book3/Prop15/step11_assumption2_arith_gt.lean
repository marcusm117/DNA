import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_15_step11_assumption2_arith_gt
    (l m k f : Point)
    (h_lm_gt_kf_sq : |(l─m)| * |(l─m)| > |(k─f)| * |(k─f)|) :
    |(l─m)| > |(k─f)| := by
  have h_0lm := segment_gte_zero (l─m)
  have h_0kf := segment_gte_zero (k─f)
  rcases le_or_lt |(l─m)| |(k─f)| with h | h
  · -- |l─m| ≤ |k─f| implies |l─m|² ≤ |k─f|², contradicting h_lm_gt_kf_sq
    have h_sq : |(l─m)| * |(l─m)| ≤ |(k─f)| * |(k─f)| :=
      mul_le_mul h h h_0lm h_0kf
    linarith
  · exact h

end Elements.Book3
