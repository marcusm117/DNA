import SystemE
import Helpers.Angle
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step21_amk (a b c d e k m : Point) (AB AE BL CH MN : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE) (h_m_ae : m.onLine AE)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_b_bl : b.onLine BL) (h_k_bl : k.onLine BL)
    (h_k_mn : k.onLine MN) (h_m_mn : m.onLine MN)
    (h_bl_ae : ¬(BL.intersectsLine AE)) (h_mn_ab : ¬(MN.intersectsLine AB))
    (h_dae : ∠ d:a:e = ∟) (h_ame : between a m e) :
    ∠ a:m:k = ∟ := by
  have h_e_off_ab : ¬(e.onLine AB) := by
    euclid_apply (Elements.offLine_of_right_angle a d e AB)
    euclid_finish
  have h_b_off_ae : ¬(b.onLine AE) := by
    euclid_apply (Elements.offLine_of_two_points b a e AB AE)
    euclid_finish
  have hne_bl_ae : BL ≠ AE := fun heq => h_b_off_ae (heq ▸ h_b_bl)
  have h_kb_ae : k.sameSide b AE := by
    euclid_apply (Elements.sameSide_of_parallel_both k b BL AE)
    euclid_finish
  have h_bd_ae : b.sameSide d AE := by
    euclid_finish
  have h_kd_ae : k.sameSide d AE := by
    euclid_finish
  euclid_apply (Elements.corresponding_angle e d k a m MN AB AE)
  euclid_finish

end Elements.Book2
