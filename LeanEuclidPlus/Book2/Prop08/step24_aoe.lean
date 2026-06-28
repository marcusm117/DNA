import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step24_aoe (a b d e k o q : Point)
    (AB AE ED OP : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE) (h_o_ae : o.onLine AE)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_o_op : o.onLine OP) (h_q_op : q.onLine OP)
    (h_op_ab : ¬(OP.intersectsLine AB))
    (h_dae : ∠ d:a:e = ∟)
    (h_qkd : between q k d) (h_kqe : between k q e) :
    between a o e := by
  have h_e_off_ab : ¬(e.onLine AB) := by
    euclid_apply (Elements.offLine_of_right_angle a d e AB)
    euclid_finish
  have h_q_off_ab : ¬(q.onLine AB) := by
    euclid_finish
  have hne_op_ab : OP ≠ AB := fun heq => h_q_off_ab (heq ▸ h_q_op)
  have h_eqd : between e q d := by
    euclid_finish
  have h_ad_op : a.sameSide d OP := by
    euclid_apply (Elements.sameSide_of_parallel_both a d AB OP)
    euclid_finish
  euclid_apply (pasch_3 e q d OP)
  have h_ae_opp : ¬(a.sameSide e OP) := by
    euclid_finish
  euclid_apply (pasch_4 a o e OP AE)
  euclid_finish

end Elements.Book2
