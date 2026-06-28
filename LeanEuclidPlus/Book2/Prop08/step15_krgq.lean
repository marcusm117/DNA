import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step15_krgq (a b c d e g k q r : Point)
    (AB AE BL CH ED MN OP : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_c_ch : c.onLine CH) (h_g_ch : g.onLine CH) (h_q_ch : q.onLine CH)
    (h_b_bl : b.onLine BL) (h_k_bl : k.onLine BL) (h_r_bl : r.onLine BL)
    (h_g_mn : g.onLine MN) (h_k_mn : k.onLine MN)
    (h_q_op : q.onLine OP) (h_r_op : r.onLine OP)
    (h_ch_ae : ¬(CH.intersectsLine AE)) (h_bl_ae : ¬(BL.intersectsLine AE))
    (h_mn_ab : ¬(MN.intersectsLine AB)) (h_op_ab : ¬(OP.intersectsLine AB))
    (h_dae : ∠ d:a:e = ∟)
    (h_chbl : ¬(CH.intersectsLine BL)) (h_mnop : ¬(MN.intersectsLine OP))
    (h_qkd : between q k d) :
    formParallelogram k r g q BL CH MN OP := by
  have h_e_off_ab : ¬(e.onLine AB) := by
    euclid_apply (Elements.offLine_of_right_angle a d e AB)
    euclid_finish
  have h_k_off_ab : ¬(k.onLine AB) := by
    euclid_finish
  have hne_mn_ab : MN ≠ AB := fun heq => h_k_off_ab (heq ▸ h_k_mn)
  have h_q_off_mn : ¬(q.onLine MN) := by
    euclid_finish
  have hne_mn_op : MN ≠ OP := fun heq => h_q_off_mn (heq ▸ h_q_op)
  have h_c_off_bl : ¬(c.onLine BL) := by
    euclid_finish
  have hne_ch_bl : CH ≠ BL := fun heq => h_c_off_bl (heq ▸ h_c_ch)
  have h_kg_op : k.sameSide g OP := by
    euclid_apply (Elements.sameSide_of_parallel_both k g MN OP)
    euclid_finish
  euclid_finish

end Elements.Book2
