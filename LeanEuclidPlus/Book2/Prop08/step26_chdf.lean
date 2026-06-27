import SystemE
import Helpers.Parallel
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- DF ∥ CH : ¬(CH.intersectsLine DF). Both are parallel to AE (CH∥AE via h_ch_ae,
   AE∥DF via h_ae_df), so by transitivity (Helpers.Parallel.not_intersects_trans
   CH AE DF). Reused by the CH/BL-separation betweenness leaves. -/
set_option systemE.solverTime 30 in
theorem helper_2_8_step26_chdf (a b c d e g : Point)
    (AB AE CH DF ED : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_c_ch : c.onLine CH) (h_g_ch : g.onLine CH)
    (h_d_df : d.onLine DF)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_ch_ae : ¬(CH.intersectsLine AE)) (h_ae_df : ¬(AE.intersectsLine DF))
    (h_dae : ∠ d:a:e = ∟) :
    ¬(CH.intersectsLine DF) := by
  have h_a_off_ch : ¬(a.onLine CH) := by
    euclid_finish
  have hne_ch_ae : CH ≠ AE := fun heq => h_a_off_ch (heq ▸ h_a_ae)
  have h_d_off_ae : ¬(d.onLine AE) := by
    euclid_apply (Elements.offLine_of_two_points d a e AB AE)
    euclid_finish
  have hne_df_ae : DF ≠ AE := fun heq => h_d_off_ae (heq ▸ h_d_df)
  have h_g_off_df : ¬(g.onLine DF) := by
    euclid_finish
  have hne_ch_df : CH ≠ DF := fun heq => h_g_off_df (heq ▸ h_g_ch)
  have h_ae_ch : ¬(AE.intersectsLine CH) := by
    euclid_finish
  euclid_apply (Elements.not_intersects_trans CH AE DF)
  euclid_finish

end Elements.Book2
