import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step15_qrhl (a b c d e h k l q r : Point)
    (AB AE BL CH ED EF OP : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_e_ef : e.onLine EF) (h_h_ef : h.onLine EF) (h_l_ef : l.onLine EF)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_c_ch : c.onLine CH) (h_q_ch : q.onLine CH) (h_h_ch : h.onLine CH)
    (h_b_bl : b.onLine BL) (h_k_bl : k.onLine BL) (h_l_bl : l.onLine BL) (h_r_bl : r.onLine BL)
    (h_q_op : q.onLine OP) (h_r_op : r.onLine OP)
    (h_ch_ae : ¬(CH.intersectsLine AE)) (h_op_ab : ¬(OP.intersectsLine AB))
    (h_dae : ∠ d:a:e = ∟)
    (h_chbl : ¬(CH.intersectsLine BL)) (h_efop : ¬(EF.intersectsLine OP))
    (h_qkd : between q k d) (h_kqe : between k q e) :
    formParallelogram q r h l OP EF CH BL := by
  have step15_qhoe_qoffab : ¬(q.onLine AB) := by sorry
  have hne_op_ab : OP ≠ AB := fun heq => step15_qhoe_qoffab (heq ▸ h_q_op)
  have step15_qhoe_eoffop : ¬(e.onLine OP) := by sorry
  have hne_ef_op : EF ≠ OP := fun heq => step15_qhoe_eoffop (heq ▸ h_e_ef)
  have step14_hqbl : h.sameSide q BL := by sorry
  euclid_finish

end Elements.Book2
