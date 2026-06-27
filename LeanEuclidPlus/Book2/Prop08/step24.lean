import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step24 (a b c d e f g h k m o q : Point)
    (AB AE BL CH DF ED EF MN OP : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE) (h_m_ae : m.onLine AE) (h_o_ae : o.onLine AE)
    (h_d_df : d.onLine DF) (h_f_df : f.onLine DF)
    (h_e_ef : e.onLine EF) (h_f_ef : f.onLine EF) (h_h_ef : h.onLine EF)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|) (h_ef_eq : |(e─f)| = |(a─d)|)
    (h_c_ch : c.onLine CH) (h_g_ch : g.onLine CH) (h_q_ch : q.onLine CH) (h_h_ch : h.onLine CH)
    (h_b_bl : b.onLine BL) (h_k_bl : k.onLine BL)
    (h_g_mn : g.onLine MN) (h_k_mn : k.onLine MN)
    (h_q_op : q.onLine OP) (h_o_op : o.onLine OP)
    (h_ch_ae : ¬(CH.intersectsLine AE)) (h_bl_ae : ¬(BL.intersectsLine AE))
    (h_mn_ab : ¬(MN.intersectsLine AB)) (h_op_ab : ¬(OP.intersectsLine AB))
    (h_ae_df : ¬(AE.intersectsLine DF)) (h_ef_ab : ¬(EF.intersectsLine AB))
    (h_dae : ∠ d:a:e = ∟) (h_aef : ∠ a:e:f = ∟) :
    Triangle.area △ o:q:h + Triangle.area △ o:h:e = |(a─c)| * |(a─c)| := by
  have step12_gkgq_ang_qkd : between q k d := by sorry
  have step12_gkgq_ang_kqe : between k q e := by sorry
  have step14_efop : ¬(EF.intersectsLine OP) := by sorry
  have step24_qoffef : ¬(q.onLine EF) := by sorry
  have hne_ef_op : EF ≠ OP := fun heq => step24_qoffef (heq ▸ h_q_op)
  have step24_aoe : between a o e := by sorry
  have step24_dfch : ¬(DF.intersectsLine CH) := by sorry
  have step24_each : e.sameSide a CH := by sorry
  have step24_fdch : f.sameSide d CH := by sorry
  have step24_efopp : ¬(e.sameSide f CH) := by sorry
  have step24_ehf : between e h f := by sorry
  have step24_ohpar : formParallelogram o q e h OP EF AE CH := by sorry
  have step24_oeh : ∠ o:e:h = ∟ := by sorry
  have step24_acqo : formParallelogram a c o q AB OP AE CH := by sorry
  have step24_oqac : |(o─q)| = |(a─c)| := by sorry
  have step24_qdae : q.sameSide d AE := by sorry
  have step24_eqd : between e q d := by sorry
  have step24_eoq : ∠ e:o:q = ∟ := by sorry
  have step24_oeoq : |(o─e)| = |(o─q)| := by sorry
  euclid_apply (rectangle_area o q e h OP EF AE CH)
  euclid_finish

end Elements.Book2
