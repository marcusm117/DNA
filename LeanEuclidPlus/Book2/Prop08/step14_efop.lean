import SystemE
import Helpers.Parallel
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step14_efop (a b c d e k q : Point)
    (AB AE BL CH ED EF OP : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_e_ef : e.onLine EF)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_c_ch : c.onLine CH) (h_q_ch : q.onLine CH)
    (h_k_bl : k.onLine BL) (h_b_bl : b.onLine BL)
    (h_q_op : q.onLine OP)
    (h_ch_ae : ¬(CH.intersectsLine AE))
    (h_ef_ab : ¬(EF.intersectsLine AB)) (h_op_ab : ¬(OP.intersectsLine AB))
    (h_dae : ∠ d:a:e = ∟)
    (h_qkd : between q k d) :
    ¬(EF.intersectsLine OP) := by
  have h_e_off_ab : ¬(e.onLine AB) := by
    euclid_apply (Elements.offLine_of_right_angle a d e AB)
    euclid_finish
  have hne_ef_ab : EF ≠ AB := fun heq => h_e_off_ab (heq ▸ h_e_ef)
  have h_q_off_ab : ¬(q.onLine AB) := by
    euclid_finish
  have hne_op_ab : OP ≠ AB := fun heq => h_q_off_ab (heq ▸ h_q_op)
  have h_q_off_ef : ¬(q.onLine EF) := by
    euclid_finish
  have hne_ef_op : EF ≠ OP := fun heq => h_q_off_ef (heq ▸ h_q_op)
  have h_ab_op : ¬(AB.intersectsLine OP) := by
    euclid_finish
  euclid_apply (Elements.not_intersects_trans EF AB OP)
  euclid_finish

end Elements.Book2
