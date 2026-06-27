import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step15_qhoe (a b c d e g h k o q : Point)
    (AB AE BL CH ED EF MN OP : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB) (h_acb : between a c b)
    (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE) (h_o_ae : o.onLine AE)
    (h_e_ef : e.onLine EF) (h_h_ef : h.onLine EF)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_c_ch : c.onLine CH) (h_g_ch : g.onLine CH) (h_q_ch : q.onLine CH) (h_h_ch : h.onLine CH)
    (h_b_bl : b.onLine BL) (h_k_bl : k.onLine BL)
    (h_g_mn : g.onLine MN) (h_k_mn : k.onLine MN)
    (h_q_op : q.onLine OP) (h_o_op : o.onLine OP)
    (h_ch_ae : ¬(CH.intersectsLine AE)) (h_bl_ae : ¬(BL.intersectsLine AE))
    (h_mn_ab : ¬(MN.intersectsLine AB)) (h_op_ab : ¬(OP.intersectsLine AB))
    (h_dae : ∠ d:a:e = ∟)
    (h_efop : ¬(EF.intersectsLine OP)) (h_qkd : between q k d) :
    formParallelogram q h o e CH AE OP EF := by
  have step12_gkgq_ang_kqe : between k q e := by sorry
  have step15_qhoe_qoffab : ¬(q.onLine AB) := by sorry
  have hne_op_ab : OP ≠ AB := fun heq => step15_qhoe_qoffab (heq ▸ h_q_op)
  have step15_qhoe_eoffop : ¬(e.onLine OP) := by sorry
  have step15_qhoe_ss : q.sameSide o EF := by sorry
  have h_c_off_ae : ¬(c.onLine AE) := by
    euclid_apply (Elements.offLine_of_two_points c a e AB AE)
    euclid_finish
  have hne_ch_ae : CH ≠ AE := fun heq => h_c_off_ae (heq ▸ h_c_ch)
  euclid_finish

end Elements.Book2
