import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step21_ame (a b c d e k m q : Point)
    (AB AE BL CH ED MN : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE) (h_m_ae : m.onLine AE)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_b_bl : b.onLine BL) (h_k_bl : k.onLine BL)
    (h_k_mn : k.onLine MN) (h_m_mn : m.onLine MN)
    (h_bl_ae : ¬(BL.intersectsLine AE)) (h_mn_ab : ¬(MN.intersectsLine AB))
    (h_dae : ∠ d:a:e = ∟)
    (h_qkd : between q k d) (h_kqe : between k q e) :
    between a m e := by
  have h_e_off_ab : ¬(e.onLine AB) := by
    euclid_apply (Elements.offLine_of_right_angle a d e AB)
    euclid_finish
  have h_k_off_ab : ¬(k.onLine AB) := by
    euclid_finish
  have hne_mn_ab : MN ≠ AB := fun heq => h_k_off_ab (heq ▸ h_k_mn)
  have h_ekd : between e k d := by
    euclid_finish
  have h_ad_mn : a.sameSide d MN := by
    euclid_apply (Elements.sameSide_of_parallel_both a d AB MN)
    euclid_finish
  euclid_apply (pasch_3 e k d MN)
  have h_ae_opp : ¬(a.sameSide e MN) := by
    euclid_finish
  euclid_apply (pasch_4 a m e MN AE)
  euclid_finish

end Elements.Book2
