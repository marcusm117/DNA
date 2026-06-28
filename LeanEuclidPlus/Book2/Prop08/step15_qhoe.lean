import SystemE
import Helpers.OffLine
import Book2.Prop08.step12_gkgq_ang_kqe
import Book2.Prop08.step15_qhoe_qoffab
import Book2.Prop08.step15_qhoe_eoffop
import Book2.Prop08.step15_qhoe_ss
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

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
  have step12_gkgq_ang_kqe : between k q e := by euclid_apply (helper_2_8_step12_gkgq_ang_kqe a b c d e g k q AB AE BL CH ED MN (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show k.onLine ED; assumption)) (by euclid_assumption "" (show q.onLine ED; assumption)) (by euclid_assumption "" (show |(a─e)| = |(a─d)|; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show g.onLine CH; assumption)) (by euclid_assumption "" (show q.onLine CH; assumption)) (by euclid_assumption "" (show b.onLine BL; assumption)) (by euclid_assumption "" (show k.onLine BL; assumption)) (by euclid_assumption "" (show g.onLine MN; assumption)) (by euclid_assumption "" (show k.onLine MN; assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(BL.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(MN.intersectsLine AB); assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)))
  have step15_qhoe_qoffab : ¬(q.onLine AB) := by euclid_apply (helper_2_8_step15_qhoe_qoffab a b d e k q AB AE ED (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show k.onLine ED; assumption)) (by euclid_assumption "" (show q.onLine ED; assumption)) (by euclid_assumption "" (show |(a─e)| = |(a─d)|; assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)) (by euclid_assumption "" (show between q k d; assumption)))
  have hne_op_ab : OP ≠ AB := fun heq => step15_qhoe_qoffab (heq ▸ h_q_op)
  have step15_qhoe_eoffop : ¬(e.onLine OP) := by euclid_apply (helper_2_8_step15_qhoe_eoffop d e k q AB ED OP (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show k.onLine ED; assumption)) (by euclid_assumption "" (show q.onLine ED; assumption)) (by euclid_assumption "" (show q.onLine OP; assumption)) (by euclid_assumption "" (show ¬(OP.intersectsLine AB); assumption)) (by euclid_assumption "" (show between k q e; assumption)) (by euclid_assumption "" (show OP ≠ AB; assumption)))
  have step15_qhoe_ss : q.sameSide o EF := by euclid_apply (helper_2_8_step15_qhoe_ss e o q EF OP (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show q.onLine OP; assumption)) (by euclid_assumption "" (show o.onLine OP; assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine OP); assumption)) (by euclid_assumption "" (show ¬(e.onLine OP); assumption)))
  have h_c_off_ae : ¬(c.onLine AE) := by
    euclid_apply (Elements.offLine_of_two_points c a e AB AE)
    euclid_finish
  have hne_ch_ae : CH ≠ AE := fun heq => h_c_off_ae (heq ▸ h_c_ch)
  euclid_finish

end Elements.Book2
