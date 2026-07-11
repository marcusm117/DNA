import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step7 (g d h : Point)
    (hd_bet_gdh : between g d h)
    (step6 : |(g─d)| > |(g─h)|)
    : False := by
  have hbet_dist : |(g─d)| + |(d─h)| = |(g─h)| := between_if g d h hd_bet_gdh
  have hdh_pos : |(d─h)| ≥ 0 := by euclid_finish
  linarith

end Elements.Book3
