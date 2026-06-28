import SystemE
import Helpers.Parallel
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step4_bdkn_bldf (a b d e f : Point) (AB AE BL DF : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_abd : between a b d)
    (h_d_ab : d.onLine AB) (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_d_df : d.onLine DF) (h_f_df : f.onLine DF)
    (h_ae_eq : |(a─e)| = |(a─d)|) (h_df_eq : |(d─f)| = |(a─d)|)
    (h_b_bl : b.onLine BL) (h_bl_ae : ¬(BL.intersectsLine AE))
    (h_ae_df : ¬(AE.intersectsLine DF)) (h_dae : ∠ d:a:e = ∟)
    (h_adf : ∠ a:d:f = ∟) :
    ¬(BL.intersectsLine DF) := by
  have h_e_off_ab : ¬(e.onLine AB) := by
    euclid_apply (Elements.offLine_of_right_angle a d e AB)
    euclid_finish
  have h_f_off_ab : ¬(f.onLine AB) := by
    euclid_apply (Elements.offLine_of_right_angle d a f AB)
    euclid_finish
  have h_b_off_ae : ¬(b.onLine AE) := by
    euclid_apply (Elements.offLine_of_two_points b a e AB AE)
    euclid_finish
  have h_d_off_ae : ¬(d.onLine AE) := by
    euclid_apply (Elements.offLine_of_two_points d a e AB AE)
    euclid_finish
  have h_b_off_df : ¬(b.onLine DF) := by
    euclid_apply (Elements.offLine_of_two_points b d f AB DF)
    euclid_finish
  have hne_bl_ae : BL ≠ AE := fun heq => h_b_off_ae (heq ▸ h_b_bl)
  have hne_ae_df : AE ≠ DF := fun heq => h_d_off_ae (heq ▸ h_d_df)
  have hne_bl_df : BL ≠ DF := fun heq => h_b_off_df (heq ▸ h_b_bl)
  euclid_apply (Elements.not_intersects_trans BL AE DF)
  euclid_finish

end Elements.Book2
