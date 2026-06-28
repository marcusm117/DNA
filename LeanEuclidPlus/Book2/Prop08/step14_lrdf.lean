import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step14_lrdf (a b d e f l r : Point) (AB AE BL DF : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB)
    (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_d_df : d.onLine DF) (h_f_df : f.onLine DF)
    (h_ae_eq : |(a─e)| = |(a─d)|) (h_df_eq : |(d─f)| = |(a─d)|)
    (h_l_bl : l.onLine BL) (h_r_bl : r.onLine BL) (h_b_bl : b.onLine BL)
    (h_bl_ae : ¬(BL.intersectsLine AE)) (h_ae_df : ¬(AE.intersectsLine DF))
    (h_dae : ∠ d:a:e = ∟) (h_adf : ∠ a:d:f = ∟)
    (h_bl_df : ¬(BL.intersectsLine DF)) :
    l.sameSide r DF := by
  have h_b_off_df : ¬(b.onLine DF) := by
    euclid_apply (Elements.offLine_of_two_points b d f AB DF)
    euclid_finish
  have hne_bl_df : BL ≠ DF := fun heq => h_b_off_df (heq ▸ h_b_bl)
  euclid_apply (Elements.sameSide_of_parallel_both l r BL DF)
  euclid_finish

end Elements.Book2
