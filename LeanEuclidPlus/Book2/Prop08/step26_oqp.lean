import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- between o q p : q = CH ∩ OP lies between o and p on OP. CH separates o (AE side)
   from p (DF side): between a c d, c on CH ⟹ a,d opposite sides of CH; o~a (AE∥CH),
   p~d (DF∥CH). pasch_4 o q p CH OP. -/
theorem helper_2_8_step26_oqp (a b c d e k o q p : Point)
    (AB AE CH DF OP ED : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE) (h_o_ae : o.onLine AE)
    (h_d_df : d.onLine DF) (h_p_df : p.onLine DF)
    (h_c_ch : c.onLine CH) (h_q_ch : q.onLine CH)
    (h_o_op : o.onLine OP) (h_q_op : q.onLine OP) (h_p_op : p.onLine OP)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_ch_ae : ¬(CH.intersectsLine AE)) (h_ae_df : ¬(AE.intersectsLine DF))
    (h_chdf : ¬(CH.intersectsLine DF)) (h_op_ab : ¬(OP.intersectsLine AB))
    (h_dae : ∠ d:a:e = ∟) (h_qkd : between q k d) (h_kqe : between k q e) :
    between o q p := by
  have h_op_opp : ¬(o.sameSide p CH) := by
    euclid_finish
  euclid_apply (pasch_4 o q p CH OP)
  euclid_finish

end Elements.Book2
