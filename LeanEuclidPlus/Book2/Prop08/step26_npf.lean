import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- between n p f : p = OP ∩ DF lies between n and f on DF. OP separates n (below, MN
   side) from f (above, EF side). Diagonal ED crosses OP at q; e,d opposite sides of OP;
   n~k (MN∥OP), k~d (k between q∈OP and d), f~e (EF∥OP). -/
theorem helper_2_8_step26_npf (a b c d e f k n p q : Point)
    (AB AE DF EF ED MN OP : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_d_df : d.onLine DF) (h_f_df : f.onLine DF) (h_n_df : n.onLine DF) (h_p_df : p.onLine DF)
    (h_e_ef : e.onLine EF) (h_f_ef : f.onLine EF)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_k_mn : k.onLine MN) (h_n_mn : n.onLine MN)
    (h_q_op : q.onLine OP) (h_p_op : p.onLine OP)
    (h_mn_ab : ¬(MN.intersectsLine AB)) (h_op_ab : ¬(OP.intersectsLine AB))
    (h_ae_df : ¬(AE.intersectsLine DF)) (h_mnop : ¬(MN.intersectsLine OP))
    (h_efop : ¬(EF.intersectsLine OP)) (h_dae : ∠ d:a:e = ∟)
    (h_qkd : between q k d) (h_kqe : between k q e) :
    between n p f := by
  have h_fe_op : f.sameSide e OP := by
    euclid_apply (Elements.sameSide_of_parallel_both f e EF OP)
    euclid_finish
  have h_nk_op : n.sameSide k OP := by
    euclid_apply (Elements.sameSide_of_parallel_both n k MN OP)
    euclid_finish
  have h_npf_opp : ¬(n.sameSide f OP) := by
    euclid_finish
  euclid_apply (pasch_4 n p f OP DF)
  euclid_finish

end Elements.Book2
