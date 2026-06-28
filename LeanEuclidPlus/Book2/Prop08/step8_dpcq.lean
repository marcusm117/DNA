import SystemE
import Book2.Prop08.step8_dpcq_qoffab
import Book2.Prop08.step8_dpcq_dfch
import Book2.Prop08.step8_dpcq_qoffdf
import Book2.Prop08.step8_dpcq_ss
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step8_dpcq (a b c d e f q p : Point)
    (AB AE CH DF ED OP : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d)
    (h_d_ab : d.onLine AB) (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_d_df : d.onLine DF) (h_f_df : f.onLine DF)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|) (h_df_eq : |(d─f)| = |(a─d)|)
    (h_c_ch : c.onLine CH) (h_q_ch : q.onLine CH)
    (h_q_op : q.onLine OP) (h_p_op : p.onLine OP) (h_p_df : p.onLine DF)
    (h_ch_ae : ¬(CH.intersectsLine AE)) (h_op_ab : ¬(OP.intersectsLine AB))
    (h_ae_df : ¬(AE.intersectsLine DF))
    (h_dae : ∠ d:a:e = ∟) (h_adf : ∠ a:d:f = ∟) :
    formParallelogram d p c q DF CH AB OP := by
  have step8_dpcq_qoffab : ¬(q.onLine AB) := by euclid_apply (helper_2_8_step8_dpcq_qoffab a b c d e q AB AE CH ED (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show q.onLine ED; assumption)) (by euclid_assumption "" (show |(a─e)| = |(a─d)|; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show q.onLine CH; assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine AE); assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)))
  have step8_dpcq_dfch : ¬(DF.intersectsLine CH) := by euclid_apply (helper_2_8_step8_dpcq_dfch a b c d e q AB AE CH DF ED (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show q.onLine ED; assumption)) (by euclid_assumption "" (show |(a─e)| = |(a─d)|; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show q.onLine CH; assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(AE.intersectsLine DF); assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)) (by euclid_assumption "" (show ¬(q.onLine AB); assumption)))
  have step8_dpcq_qoffdf : ¬(q.onLine DF) := by euclid_apply (helper_2_8_step8_dpcq_qoffdf a b c d q AB CH DF (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show q.onLine CH; assumption)) (by euclid_assumption "" (show ¬(q.onLine AB); assumption)) (by euclid_assumption "" (show ¬(DF.intersectsLine CH); assumption)))
  have step8_dpcq_ss : d.sameSide c OP := by euclid_apply (helper_2_8_step8_dpcq_ss c d q AB OP (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show q.onLine OP; assumption)) (by euclid_assumption "" (show ¬(OP.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(q.onLine AB); assumption)))
  have h_ab_op : ¬(AB.intersectsLine OP) := by
    intro h
    euclid_apply (intersection_symm AB OP)
    euclid_finish
  have h_p_ne_q : p ≠ q := by
    intro hpq
    exact step8_dpcq_qoffdf (hpq ▸ h_p_df)
  euclid_finish

end Elements.Book2
