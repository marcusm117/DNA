import SystemE
import Book.Prop43
import Helpers.Area
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step15 (a b c d e g k h l m o q r : Point)
    (AB AE BL CH ED EF MN OP : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE) (h_m_ae : m.onLine AE) (h_o_ae : o.onLine AE)
    (h_e_ef : e.onLine EF) (h_h_ef : h.onLine EF) (h_l_ef : l.onLine EF)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_c_ch : c.onLine CH) (h_g_ch : g.onLine CH) (h_q_ch : q.onLine CH) (h_h_ch : h.onLine CH)
    (h_b_bl : b.onLine BL) (h_k_bl : k.onLine BL) (h_r_bl : r.onLine BL) (h_l_bl : l.onLine BL)
    (h_g_mn : g.onLine MN) (h_k_mn : k.onLine MN) (h_m_mn : m.onLine MN)
    (h_q_op : q.onLine OP) (h_r_op : r.onLine OP) (h_o_op : o.onLine OP)
    (h_ch_ae : ¬(CH.intersectsLine AE)) (h_bl_ae : ¬(BL.intersectsLine AE))
    (h_mn_ab : ¬(MN.intersectsLine AB)) (h_op_ab : ¬(OP.intersectsLine AB))
    (h_ef_ab : ¬(EF.intersectsLine AB))
    (h_dae : ∠ d:a:e = ∟) :
    Triangle.area △ m:g:q + Triangle.area △ m:q:o =
      Triangle.area △ q:r:l + Triangle.area △ q:l:h := by
  have step12_gkgq_ang_qkd : between q k d := by sorry
  have step12_gkgq_ang_kqe : between k q e := by sorry
  have step7_gkqr_chbl : ¬(CH.intersectsLine BL) := by sorry
  have step13_mnop : ¬(MN.intersectsLine OP) := by sorry
  have step14_efop : ¬(EF.intersectsLine OP) := by sorry
  have step15_mnef : ¬(MN.intersectsLine EF) := by sorry
  have step15_klme : formParallelogram k l m e BL AE MN EF := by sorry
  have step15_krgq : formParallelogram k r g q BL CH MN OP := by sorry
  have step15_qhoe : formParallelogram q h o e CH AE OP EF := by sorry
  have step15_qrhl : formParallelogram q r h l OP EF CH BL := by sorry
  have step13_mogq : formParallelogram m o g q AE CH MN OP := by sorry
  have step15_ke : distinctPointsOnLine k e ED := by sorry
  have step15_krl : between k r l := by sorry
  euclid_apply (Elements.Book1.proposition_43 k m e l g h o r q BL AE MN EF ED CH OP)
  euclid_apply (Elements.parallelogram_area' q r h l OP EF CH BL)
  euclid_apply (Elements.parallelogram_area' m o g q AE CH MN OP)
  euclid_finish

end Elements.Book2
