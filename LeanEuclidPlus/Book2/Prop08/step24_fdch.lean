import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step24_fdch (a b c d e f : Point)
    (AB AE CH DF : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_d_df : d.onLine DF) (h_f_df : f.onLine DF)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_c_ch : c.onLine CH)
    (h_ch_ae : ¬(CH.intersectsLine AE))
    (h_dae : ∠ d:a:e = ∟)
    (h_dfch : ¬(DF.intersectsLine CH)) :
    f.sameSide d CH := by
  have h_e_off_ab : ¬(e.onLine AB) := by
    euclid_apply (Elements.offLine_of_right_angle a d e AB)
    euclid_finish
  have h_a_off_ch : ¬(a.onLine CH) := by
    euclid_finish
  have h_d_off_ch : ¬(d.onLine CH) := by
    euclid_finish
  have hne_df_ch : DF ≠ CH := fun heq => h_d_off_ch (heq ▸ h_d_df)
  euclid_apply (Elements.sameSide_of_parallel_both f d DF CH)
  euclid_finish

end Elements.Book2
