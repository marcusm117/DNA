import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- Bottom-rest formParallelogram c d g n (c-d on AB, g-n on MN, c-g on CH, d-n on DF).
   Used by step26_btm2. Needs CH∥DF (h_chdf). -/
theorem helper_2_8_step26_btm2_par (a b c d e m g n : Point)
    (AB AE CH DF MN ED : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_c_ch : c.onLine CH) (h_g_ch : g.onLine CH)
    (h_d_df : d.onLine DF) (h_n_df : n.onLine DF)
    (h_m_mn : m.onLine MN) (h_g_mn : g.onLine MN) (h_n_mn : n.onLine MN)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_ame : between a m e)
    (h_mn_ab : ¬(MN.intersectsLine AB)) (h_ae_df : ¬(AE.intersectsLine DF))
    (h_chdf : ¬(CH.intersectsLine DF)) (h_dae : ∠ d:a:e = ∟) :
    formParallelogram c d g n AB MN CH DF := by
  have h_e_off_ab : ¬(e.onLine AB) := by
    euclid_apply (Elements.offLine_of_right_angle a d e AB)
    euclid_finish
  have h_g_off_ab : ¬(g.onLine AB) := by
    have h_m_off_ab : ¬(m.onLine AB) := by
      euclid_finish
    have hne_mn_ab : MN ≠ AB := fun heq => h_m_off_ab (heq ▸ h_m_mn)
    exact Elements.offLine_of_parallel_simple g MN AB h_g_mn hne_mn_ab h_mn_ab
  have hne_mn_ab : MN ≠ AB := fun heq => h_g_off_ab (heq ▸ h_g_mn)
  have h_cd_mn : c.sameSide d MN := by
    euclid_apply (Elements.sameSide_of_parallel_both c d AB MN)
    euclid_finish
  euclid_finish

end Elements.Book2
