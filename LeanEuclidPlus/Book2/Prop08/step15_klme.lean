import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step15_klme (a b c d e k l m q : Point)
    (AB AE BL CH ED EF MN : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE) (h_m_ae : m.onLine AE)
    (h_e_ef : e.onLine EF) (h_l_ef : l.onLine EF)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_b_bl : b.onLine BL) (h_k_bl : k.onLine BL) (h_l_bl : l.onLine BL)
    (h_k_mn : k.onLine MN) (h_m_mn : m.onLine MN)
    (h_bl_ae : ¬(BL.intersectsLine AE)) (h_ef_ab : ¬(EF.intersectsLine AB))
    (h_dae : ∠ d:a:e = ∟)
    (h_mnef : ¬(MN.intersectsLine EF)) (h_qkd : between q k d) :
    formParallelogram k l m e BL AE MN EF := by
  have h_e_off_ab : ¬(e.onLine AB) := by
    euclid_apply (Elements.offLine_of_right_angle a d e AB)
    euclid_finish
  have hne_ef_ab : EF ≠ AB := fun heq => h_e_off_ab (heq ▸ h_e_ef)
  have h_k_off_ef : ¬(k.onLine EF) := by
    euclid_finish
  have hne_mn_ef : MN ≠ EF := fun heq => h_k_off_ef (heq ▸ h_k_mn)
  have h_km_ef : k.sameSide m EF := by
    euclid_apply (Elements.sameSide_of_parallel_both k m MN EF)
    euclid_finish
  euclid_finish

end Elements.Book2
