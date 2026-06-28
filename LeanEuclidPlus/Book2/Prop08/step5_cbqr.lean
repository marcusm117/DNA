import SystemE
import Book2.Prop08.step5_cbqr_abop
import Book2.Prop08.step5_cbqr_chbl
import Book2.Prop08.step5_cbqr_bner
import Book2.Prop08.step5_cbqr_ss
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step5_cbqr (a b c d e f q r p : Point)
    (AB AE BL CH DF ED OP : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d)
    (h_d_ab : d.onLine AB) (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_d_df : d.onLine DF) (h_f_df : f.onLine DF)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|) (h_df_eq : |(d─f)| = |(a─d)|)
    (h_c_ch : c.onLine CH) (h_q_ch : q.onLine CH)
    (h_b_bl : b.onLine BL) (h_r_bl : r.onLine BL)
    (h_q_op : q.onLine OP) (h_r_op : r.onLine OP) (h_p_op : p.onLine OP)
    (h_p_df : p.onLine DF)
    (h_ch_ae : ¬(CH.intersectsLine AE)) (h_bl_ae : ¬(BL.intersectsLine AE))
    (h_op_ab : ¬(OP.intersectsLine AB)) (h_ae_df : ¬(AE.intersectsLine DF))
    (h_dae : ∠ d:a:e = ∟) (h_adf : ∠ a:d:f = ∟)
    (h_bd_eq : |(b─d)| = |(c─b)|) :
    formParallelogram c b q r AB OP CH BL := by
  have step5_cbqr_abop : ¬(AB.intersectsLine OP) := by euclid_apply (helper_2_8_step5_cbqr_abop AB OP (by euclid_assumption "" (show ¬(OP.intersectsLine AB); assumption)))
  have step5_cbqr_chbl : ¬(CH.intersectsLine BL) := by euclid_apply (helper_2_8_step5_cbqr_chbl a b c d e AB AE BL CH (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show |(a─e)| = |(a─d)|; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show b.onLine BL; assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(BL.intersectsLine AE); assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)))
  have step5_cbqr_bner : b ≠ r := by euclid_apply (helper_2_8_step5_cbqr_bner a b c d e q r AB AE CH ED OP (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show q.onLine ED; assumption)) (by euclid_assumption "" (show |(a─e)| = |(a─d)|; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show q.onLine CH; assumption)) (by euclid_assumption "" (show q.onLine OP; assumption)) (by euclid_assumption "" (show r.onLine OP; assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(AB.intersectsLine OP); assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)))
  have step5_cbqr_ss : c.sameSide q BL := by euclid_apply (helper_2_8_step5_cbqr_ss a b c d e q AB AE BL CH (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show |(a─e)| = |(a─d)|; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show q.onLine CH; assumption)) (by euclid_assumption "" (show b.onLine BL; assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine AE); assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine BL); assumption)))
  euclid_finish

end Elements.Book2
