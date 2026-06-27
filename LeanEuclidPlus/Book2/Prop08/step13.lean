import SystemE
import Book.Prop36
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step13 (a b c d e g k m o q : Point)
    (AB AE BL CH ED MN OP : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE) (h_m_ae : m.onLine AE) (h_o_ae : o.onLine AE)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_c_ch : c.onLine CH) (h_g_ch : g.onLine CH) (h_q_ch : q.onLine CH)
    (h_b_bl : b.onLine BL) (h_k_bl : k.onLine BL)
    (h_g_mn : g.onLine MN) (h_k_mn : k.onLine MN) (h_m_mn : m.onLine MN)
    (h_o_op : o.onLine OP) (h_q_op : q.onLine OP)
    (h_ch_ae : ¬(CH.intersectsLine AE)) (h_bl_ae : ¬(BL.intersectsLine AE))
    (h_mn_ab : ¬(MN.intersectsLine AB)) (h_op_ab : ¬(OP.intersectsLine AB))
    (h_dae : ∠ d:a:e = ∟)
    (h_cg_gq : |(c─g)| = |(g─q)|) :
    Triangle.area △ a:c:g + Triangle.area △ a:g:m =
      Triangle.area △ m:g:q + Triangle.area △ m:q:o := by
  have step12_gkgq_ang_qkd : between q k d := by sorry
  have step13_mnop : ¬(MN.intersectsLine OP) := by sorry
  have step13_acgm : formParallelogram a m c g AE CH AB MN := by sorry
  have step13_mogq : formParallelogram m o g q AE CH MN OP := by sorry
  have step13_amo : between a m o := by sorry
  euclid_apply (Elements.Book1.proposition_36 a c g m m g q o AE CH AB MN MN OP)
  euclid_finish

end Elements.Book2
