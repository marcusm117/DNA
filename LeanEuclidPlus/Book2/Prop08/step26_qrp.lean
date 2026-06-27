import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- between q r p : r = BL ∩ OP lies between q and p on OP. BL separates q (CH side)
   from p (DF side): between c b d, b on BL ⟹ c,d opposite sides of BL; q~c (CH∥BL),
   p~d (DF∥BL). pasch_4 q r p BL OP. -/
set_option systemE.solverTime 30 in
theorem helper_2_8_step26_qrp (a b c d e k q r p : Point)
    (AB AE CH BL DF OP ED : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_q_ch : q.onLine CH) (h_c_ch : c.onLine CH)
    (h_r_bl : r.onLine BL) (h_b_bl : b.onLine BL)
    (h_p_df : p.onLine DF) (h_d_df : d.onLine DF)
    (h_q_op : q.onLine OP) (h_r_op : r.onLine OP) (h_p_op : p.onLine OP)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_ch_ae : ¬(CH.intersectsLine AE)) (h_bl_ae : ¬(BL.intersectsLine AE))
    (h_ae_df : ¬(AE.intersectsLine DF)) (h_chbl : ¬(CH.intersectsLine BL))
    (h_bldf : ¬(BL.intersectsLine DF)) (h_op_ab : ¬(OP.intersectsLine AB))
    (h_dae : ∠ d:a:e = ∟) (h_qkd : between q k d) (h_kqe : between k q e) :
    between q r p := by
  have h_qc_bl : q.sameSide c BL := by
    euclid_apply (Elements.sameSide_of_parallel_both q c CH BL)
    euclid_finish
  have h_pd_bl : p.sameSide d BL := by
    euclid_apply (Elements.sameSide_of_parallel_both p d DF BL)
    euclid_finish
  have h_qp_opp : ¬(q.sameSide p BL) := by
    euclid_finish
  euclid_apply (pasch_4 q r p BL OP)
  euclid_finish

end Elements.Book2
