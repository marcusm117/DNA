import SystemE
import Helpers.Parallel
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step8_dpcq_dfch (a b c d e q : Point)
    (AB AE CH DF ED : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d)
    (h_d_ab : d.onLine AB) (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_d_df : d.onLine DF)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_c_ch : c.onLine CH) (h_q_ch : q.onLine CH)
    (h_ch_ae : ¬(CH.intersectsLine AE)) (h_ae_df : ¬(AE.intersectsLine DF))
    (h_dae : ∠ d:a:e = ∟) (h_q_off_ab : ¬(q.onLine AB)) :
    ¬(DF.intersectsLine CH) := by
  have h_df_ae : ¬(DF.intersectsLine AE) := by
    intro h
    euclid_apply (intersection_symm DF AE)
    euclid_finish
  have h_ae_ch : ¬(AE.intersectsLine CH) := by
    intro h
    euclid_apply (intersection_symm AE CH)
    euclid_finish
  have h_e_off_ab : ¬(e.onLine AB) := by
    euclid_apply (Elements.offLine_of_right_angle a d e AB)
    euclid_finish
  have h_c_off_ae : ¬(c.onLine AE) := by
    euclid_apply (Elements.offLine_of_two_points c a e AB AE)
    euclid_finish
  have h_d_off_ae : ¬(d.onLine AE) := by
    euclid_apply (Elements.offLine_of_two_points d a e AB AE)
    euclid_finish
  have h_d_off_ch : ¬(d.onLine CH) := by
    euclid_apply (Elements.offLine_of_two_points d c q AB CH)
    euclid_finish
  have hne_df_ae : DF ≠ AE := fun heq => h_d_off_ae (heq ▸ h_d_df)
  have hne_ae_ch : AE ≠ CH := fun heq => h_c_off_ae (heq ▸ h_c_ch)
  have hne_df_ch : DF ≠ CH := fun heq => h_d_off_ch (heq ▸ h_d_df)
  euclid_apply (Elements.not_intersects_trans DF AE CH)
  euclid_finish

end Elements.Book2
