import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step24_acqo (a b c d e k o q : Point)
    (AB AE CH ED OP : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE) (h_o_ae : o.onLine AE)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_c_ch : c.onLine CH) (h_q_ch : q.onLine CH)
    (h_q_op : q.onLine OP) (h_o_op : o.onLine OP)
    (h_ch_ae : ¬(CH.intersectsLine AE)) (h_op_ab : ¬(OP.intersectsLine AB))
    (h_dae : ∠ d:a:e = ∟)
    (h_qkd : between q k d) :
    formParallelogram a c o q AB OP AE CH := by
  have h_e_off_ab : ¬(e.onLine AB) := by
    euclid_apply (Elements.offLine_of_right_angle a d e AB)
    euclid_finish
  have h_q_off_ab : ¬(q.onLine AB) := by
    euclid_finish
  have hne_op_ab : OP ≠ AB := fun heq => h_q_off_ab (heq ▸ h_q_op)
  have h_a_off_ch : ¬(a.onLine CH) := by
    euclid_finish
  have hne_ch_ae : CH ≠ AE := fun heq => h_a_off_ch (heq ▸ h_a_ae)
  have h_ao_ch : a.sameSide o CH := by
    euclid_apply (Elements.sameSide_of_parallel_both a o AE CH)
    euclid_finish
  euclid_finish

end Elements.Book2
