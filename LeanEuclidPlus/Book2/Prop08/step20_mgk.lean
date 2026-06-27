import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step20_mgk (a b c d e g k m : Point)
    (AB AE BL CH MN : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE) (h_m_ae : m.onLine AE)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_c_ch : c.onLine CH) (h_g_ch : g.onLine CH)
    (h_b_bl : b.onLine BL) (h_k_bl : k.onLine BL)
    (h_g_mn : g.onLine MN) (h_k_mn : k.onLine MN) (h_m_mn : m.onLine MN)
    (h_ch_ae : ¬(CH.intersectsLine AE)) (h_bl_ae : ¬(BL.intersectsLine AE))
    (h_mn_ab : ¬(MN.intersectsLine AB))
    (h_dae : ∠ d:a:e = ∟)
    (h_chbl : ¬(CH.intersectsLine BL)) :
    between m g k := by
  have h_e_off_ab : ¬(e.onLine AB) := by
    euclid_apply (Elements.offLine_of_right_angle a d e AB)
    euclid_finish
  have h_c_off_ae : ¬(c.onLine AE) := by
    euclid_apply (Elements.offLine_of_two_points c a e AB AE)
    euclid_finish
  have hne_ch_ae : CH ≠ AE := fun heq => h_c_off_ae (heq ▸ h_c_ch)
  have h_b_off_ae : ¬(b.onLine AE) := by
    euclid_apply (Elements.offLine_of_two_points b a e AB AE)
    euclid_finish
  have hne_bl_ae : BL ≠ AE := fun heq => h_b_off_ae (heq ▸ h_b_bl)
  have h_c_off_bl : ¬(c.onLine BL) := by
    euclid_finish
  have hne_ch_bl : CH ≠ BL := fun heq => h_c_off_bl (heq ▸ h_c_ch)
  have h_am_ch : a.sameSide m CH := by
    euclid_apply (Elements.sameSide_of_parallel_both a m AE CH)
    euclid_finish
  have h_kb_ch : k.sameSide b CH := by
    euclid_apply (Elements.sameSide_of_parallel_both k b BL CH)
    euclid_finish
  euclid_apply (pasch_3 a c b CH)
  have h_mk_opp : ¬(m.sameSide k CH) := by
    euclid_finish
  euclid_apply (pasch_4 m g k CH MN)
  euclid_finish

end Elements.Book2
