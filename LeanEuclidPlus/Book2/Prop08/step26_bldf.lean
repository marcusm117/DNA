import SystemE
import Helpers.Parallel
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- DF ∥ BL : ¬(BL.intersectsLine DF). Both parallel to AE (BL∥AE via h_bl_ae,
   AE∥DF via h_ae_df), by transitivity (not_intersects_trans BL AE DF). Reused by
   the BL-separation betweenness leaves (gkn, qrp, hlf). -/
theorem helper_2_8_step26_bldf (a b c d e l : Point)
    (AB AE BL DF ED : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_b_bl : b.onLine BL) (h_l_bl : l.onLine BL)
    (h_d_df : d.onLine DF)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_bl_ae : ¬(BL.intersectsLine AE)) (h_ae_df : ¬(AE.intersectsLine DF))
    (h_dae : ∠ d:a:e = ∟) :
    ¬(BL.intersectsLine DF) := by
  have h_a_off_bl : ¬(a.onLine BL) := by
    euclid_finish
  have hne_bl_ae : BL ≠ AE := fun heq => h_a_off_bl (heq ▸ h_a_ae)
  have h_d_off_ae : ¬(d.onLine AE) := by
    euclid_apply (Elements.offLine_of_two_points d a e AB AE)
    euclid_finish
  have hne_df_ae : DF ≠ AE := fun heq => h_d_off_ae (heq ▸ h_d_df)
  have h_l_off_df : ¬(l.onLine DF) := by
    euclid_finish
  have hne_bl_df : BL ≠ DF := fun heq => h_l_off_df (heq ▸ h_l_bl)
  have h_ae_bl : ¬(AE.intersectsLine BL) := by
    euclid_finish
  euclid_apply (Elements.not_intersects_trans BL AE DF)
  euclid_finish

end Elements.Book2
