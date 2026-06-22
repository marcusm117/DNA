import SystemE
import Book.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step5 (a b c d e f q r p : Point)
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
    |(q─r)| = |(r─p)| := by
  have step5_cbqr : formParallelogram c b q r AB OP CH BL := by sorry
  have step5_bdrp : formParallelogram b d r p AB OP BL DF := by sorry
  euclid_apply (line_from_points b q) as BQ
  euclid_apply (line_from_points d r) as DR
  euclid_apply (Elements.Book1.proposition_34 c b q r AB OP CH BL BQ)
  euclid_apply (Elements.Book1.proposition_34 b d r p AB OP BL DF DR)
  euclid_finish

end Elements.Book2
