import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_15_step11_assumption2_arith
    (l m n e k f g h : Point)
    (h_bisect : |(m─l)| = |(l─n)|)
    (hbetw : between m l n)
    (h_pm : |(l─m)| * |(l─m)| + |(e─l)| * |(e─l)| = |(e─m)| * |(e─m)|)
    (h_pf : |(k─f)| * |(k─f)| + |(e─k)| * |(e─k)| = |(e─f)| * |(e─f)|)
    (step11_assumption1 : |(m─e)| = |(f─e)| ∧ |(e─n)| = |(e─g)|)
    (step2_assumption1 : |(e─h)| < |(e─k)|)
    (step3 : |(e─l)| = |(e─h)|)
    (h_fg_le : |(f─g)| ≤ |(k─f)| + |(k─f)|) :
    |(m─n)| > |(f─g)| := by
  -- Fast inline intermediate steps
  have h_em_ef : |(e─m)| = |(e─f)| := by
    linarith [step11_assumption1.1, segment_symmetric e m, segment_symmetric f e]
  have h_em_ef_sq : |(e─m)| * |(e─m)| = |(e─f)| * |(e─f)| := by rw [h_em_ef]
  have h_el_lt_ek : |(e─l)| < |(e─k)| := by linarith [step3, step2_assumption1]
  -- Sub-node: |e─l|² < |e─k|²  (nlinarith in small context leaf)
  have step11_assumption2_arith_el_sq_lt :
      |(e─l)| * |(e─l)| < |(e─k)| * |(e─k)| := by sorry
  -- Fast linarith: |l─m|² > |k─f|² (no nlinarith needed)
  have h_lm_gt_kf_sq : |(l─m)| * |(l─m)| > |(k─f)| * |(k─f)| := by
    linarith [h_pm, h_pf, h_em_ef_sq, step11_assumption2_arith_el_sq_lt]
  -- Sub-node: |l─m| > |k─f|  (nlinarith in small context leaf)
  have step11_assumption2_arith_gt :
      |(l─m)| > |(k─f)| := by sorry
  -- Fast arithmetic: |m─n| = 2|m─l|
  have h_mn_sum : |(m─l)| + |(l─n)| = |(m─n)| := between_if m l n hbetw
  have h_mn_double : |(m─n)| = |(m─l)| + |(m─l)| := by linarith [h_bisect, h_mn_sum]
  -- |m─n| > 2|k─f|
  have h_mn_gt : |(m─n)| > |(k─f)| + |(k─f)| := by
    linarith [h_mn_double, step11_assumption2_arith_gt, segment_symmetric l m]
  -- Conclude
  linarith [h_mn_gt, h_fg_le]

end Elements.Book3
