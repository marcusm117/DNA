import SystemE
import Helpers.SameSide
import Book2.Prop08.step15_qhoe_qoffab
import Book2.Prop08.step15_qhoe_eoffop
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step15_krl (a b c d e k l q r : Point)
    (AB AE BL CH ED EF MN OP : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_e_ef : e.onLine EF) (h_l_ef : l.onLine EF)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_q_ch : q.onLine CH)
    (h_b_bl : b.onLine BL) (h_k_bl : k.onLine BL) (h_r_bl : r.onLine BL) (h_l_bl : l.onLine BL)
    (h_k_mn : k.onLine MN)
    (h_q_op : q.onLine OP) (h_r_op : r.onLine OP)
    (h_ch_ae : ¬(CH.intersectsLine AE)) (h_op_ab : ¬(OP.intersectsLine AB))
    (h_dae : ∠ d:a:e = ∟)
    (h_efop : ¬(EF.intersectsLine OP)) (h_mnop : ¬(MN.intersectsLine OP))
    (h_mnef : ¬(MN.intersectsLine EF))
    (h_qkd : between q k d) (h_kqe : between k q e) :
    between k r l := by
  have step15_qhoe_qoffab : ¬(q.onLine AB) := by euclid_apply (helper_2_8_step15_qhoe_qoffab a b d e k q AB AE ED (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show k.onLine ED; assumption)) (by euclid_assumption "" (show q.onLine ED; assumption)) (by euclid_assumption "" (show |(a─e)| = |(a─d)|; assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)) (by euclid_assumption "" (show between q k d; assumption)))
  have hne_op_ab : OP ≠ AB := fun heq => step15_qhoe_qoffab (heq ▸ h_q_op)
  have step15_qhoe_eoffop : ¬(e.onLine OP) := by euclid_apply (helper_2_8_step15_qhoe_eoffop d e k q AB ED OP (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show k.onLine ED; assumption)) (by euclid_assumption "" (show q.onLine ED; assumption)) (by euclid_assumption "" (show q.onLine OP; assumption)) (by euclid_assumption "" (show ¬(OP.intersectsLine AB); assumption)) (by euclid_assumption "" (show between k q e; assumption)) (by euclid_assumption "" (show OP ≠ AB; assumption)))
  have hne_ef_op : EF ≠ OP := fun heq => step15_qhoe_eoffop (heq ▸ h_e_ef)
  have h_le_op : l.sameSide e OP := by
    euclid_apply (Elements.sameSide_of_parallel_both l e EF OP)
    euclid_finish
  euclid_apply (pasch_3 e q k OP)
  have h_kl_opp : ¬(k.sameSide l OP) := by
    euclid_finish
  euclid_apply (pasch_4 k r l OP BL)
  euclid_finish

end Elements.Book2
