import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step20_akpar (a b c d e k m q : Point)
    (AB AE BL CH ED MN : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE) (h_m_ae : m.onLine AE)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_c_ch : c.onLine CH)
    (h_b_bl : b.onLine BL) (h_k_bl : k.onLine BL)
    (h_k_mn : k.onLine MN) (h_m_mn : m.onLine MN)
    (h_bl_ae : ¬(BL.intersectsLine AE)) (h_mn_ab : ¬(MN.intersectsLine AB))
    (h_dae : ∠ d:a:e = ∟)
    (h_qkd : between q k d) :
    formParallelogram a b m k AB MN AE BL := by
  have h_e_off_ab : ¬(e.onLine AB) := by
    euclid_apply (Elements.offLine_of_right_angle a d e AB)
    euclid_finish
  have h_k_off_ab : ¬(k.onLine AB) := by
    euclid_finish
  have hne_mn_ab : MN ≠ AB := fun heq => h_k_off_ab (heq ▸ h_k_mn)
  have h_b_off_ae : ¬(b.onLine AE) := by
    euclid_finish
  have hne_bl_ae : BL ≠ AE := fun heq => h_b_off_ae (heq ▸ h_b_bl)
  have h_am_bl : a.sameSide m BL := by
    euclid_apply (Elements.sameSide_of_parallel_both a m AE BL)
    euclid_finish
  euclid_finish

end Elements.Book2
