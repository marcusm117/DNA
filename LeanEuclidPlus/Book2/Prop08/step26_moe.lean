import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- between m o e : o = OP ∩ AE lies between m and e on AE. OP separates m (MN side,
   below) from e (EF side, above): diagonal ED crosses OP at q; m~k~d (MN∥OP), e~e
   top (EF∥OP). pasch_4 m o e OP AE. -/
theorem helper_2_8_step26_moe (a b c d e f k m o q : Point)
    (AB AE DF EF ED MN OP : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE) (h_m_ae : m.onLine AE) (h_o_ae : o.onLine AE)
    (h_d_df : d.onLine DF) (h_f_df : f.onLine DF)
    (h_e_ef : e.onLine EF) (h_f_ef : f.onLine EF)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_k_mn : k.onLine MN) (h_m_mn : m.onLine MN)
    (h_q_op : q.onLine OP) (h_o_op : o.onLine OP)
    (h_mn_ab : ¬(MN.intersectsLine AB)) (h_op_ab : ¬(OP.intersectsLine AB))
    (h_ae_df : ¬(AE.intersectsLine DF)) (h_mnop : ¬(MN.intersectsLine OP))
    (h_efop : ¬(EF.intersectsLine OP)) (h_dae : ∠ d:a:e = ∟)
    (h_qkd : between q k d) (h_kqe : between k q e) :
    between m o e := by
  have h_fe_op : f.sameSide e OP := by
    euclid_apply (Elements.sameSide_of_parallel_both f e EF OP)
    euclid_finish
  have h_mk_op : m.sameSide k OP := by
    euclid_apply (Elements.sameSide_of_parallel_both m k MN OP)
    euclid_finish
  have h_moe_opp : ¬(m.sameSide e OP) := by
    euclid_finish
  euclid_apply (pasch_4 m o e OP AE)
  euclid_finish

end Elements.Book2
