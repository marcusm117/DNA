import SystemE
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step12_gkgq_ang_gsaed (a b c d e g k q : Point) (AB AE BL CH ED MN : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d)
    (h_d_ab : d.onLine AB) (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_c_ch : c.onLine CH) (h_g_ch : g.onLine CH) (h_q_ch : q.onLine CH)
    (h_b_bl : b.onLine BL) (h_k_bl : k.onLine BL)
    (h_g_mn : g.onLine MN) (h_k_mn : k.onLine MN)
    (h_ch_ae : ¬(CH.intersectsLine AE)) (h_bl_ae : ¬(BL.intersectsLine AE))
    (h_mn_ab : ¬(MN.intersectsLine AB)) (h_dae : ∠ d:a:e = ∟)
    (h_triade : formTriangle a d e AB ED AE)
    (h_trigkq : formTriangle g k q MN ED CH)
    (h_qkd : between q k d) :
    g.sameSide a ED := by
  -- a and c are on the same side of ED: d (=ED∩AB) is not between them
  have h_c_off_ed : ¬(c.onLine ED) := by
    euclid_finish
  have h_g_off_ed : ¬(g.onLine ED) := by
    euclid_finish
  have h_acd : between a c d := by
    euclid_finish
  euclid_apply (pasch_2 d c a ED)
  have h_acs : a.sameSide c ED := by
    euclid_apply (same_side_symm c a ED)
    euclid_finish
  -- c and g are on the same side of ED: q (=ED∩CH) is not between them, since g sits on MN
  have h_k_off_ab : ¬(k.onLine AB) := by
    euclid_finish
  have hne_ab_mn : AB ≠ MN := fun heq => h_k_off_ab (heq ▸ h_k_mn)
  have h_ab_mn : ¬(AB.intersectsLine MN) := by
    euclid_finish
  have h_cdmn : c.sameSide d MN := by
    euclid_apply (Elements.sameSide_of_parallel_both c d AB MN)
    euclid_finish
  euclid_apply (pasch_3 q k d MN)
  have h_cq_opp : ¬(c.sameSide q MN) := by
    euclid_finish
  euclid_apply (pasch_4 c g q MN CH)
  euclid_apply (pasch_2 q g c ED)
  euclid_finish

end Elements.Book2
