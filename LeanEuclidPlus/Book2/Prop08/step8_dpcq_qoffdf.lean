import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step8_dpcq_qoffdf (a b c d q : Point) (AB CH DF : Line)
    (h_c_ab : c.onLine AB) (h_acb : between a c b) (h_abd : between a b d)
    (h_d_ab : d.onLine AB) (h_d_df : d.onLine DF)
    (h_c_ch : c.onLine CH) (h_q_ch : q.onLine CH)
    (h_q_off_ab : ¬(q.onLine AB)) (h_df_ch : ¬(DF.intersectsLine CH)) :
    ¬(q.onLine DF) := by
  have h_d_off_ch : ¬(d.onLine CH) := by
    euclid_apply (Elements.offLine_of_two_points d c q AB CH)
    euclid_finish
  have hne_ch_df : CH ≠ DF := by
    intro heq
    exact h_d_off_ch (heq ▸ h_d_df)
  euclid_apply (Elements.offLine_of_parallel_simple' q CH DF)
  euclid_finish

end Elements.Book2
