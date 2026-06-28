import SystemE
import Book.Prop36
import Helpers.Area
import Book2.Prop08.step7_gkqr
import Book2.Prop08.step7_knrp
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step7 (a b c d e f g k n q r p : Point)
    (AB AE BL CH DF ED MN OP : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d)
    (h_d_ab : d.onLine AB) (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_d_df : d.onLine DF) (h_f_df : f.onLine DF)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|) (h_df_eq : |(d─f)| = |(a─d)|)
    (h_c_ch : c.onLine CH) (h_g_ch : g.onLine CH) (h_q_ch : q.onLine CH)
    (h_b_bl : b.onLine BL) (h_k_bl : k.onLine BL) (h_r_bl : r.onLine BL)
    (h_g_mn : g.onLine MN) (h_k_mn : k.onLine MN) (h_n_mn : n.onLine MN)
    (h_q_op : q.onLine OP) (h_r_op : r.onLine OP) (h_p_op : p.onLine OP)
    (h_n_df : n.onLine DF) (h_p_df : p.onLine DF)
    (h_ch_ae : ¬(CH.intersectsLine AE)) (h_bl_ae : ¬(BL.intersectsLine AE))
    (h_mn_ab : ¬(MN.intersectsLine AB)) (h_op_ab : ¬(OP.intersectsLine AB))
    (h_ae_df : ¬(AE.intersectsLine DF))
    (h_dae : ∠ d:a:e = ∟) (h_adf : ∠ a:d:f = ∟)
    (h_bd_eq : |(b─d)| = |(c─b)|) (h_gk_kn : |(g─k)| = |(k─n)|)
    (h_qr_rp : |(q─r)| = |(r─p)|)
    (h_step6 : Triangle.area △ g:c:b + Triangle.area △ g:b:k =
      Triangle.area △ k:b:d + Triangle.area △ k:d:n) :
    Triangle.area △ g:k:r + Triangle.area △ g:r:q =
      Triangle.area △ k:n:p + Triangle.area △ k:p:r := by
  have step7_gkqr : formParallelogram g k q r MN OP CH BL := by euclid_apply (helper_2_8_step7_gkqr a b c d e f g k n q r p AB AE BL CH DF ED MN OP (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show k.onLine ED; assumption)) (by euclid_assumption "" (show q.onLine ED; assumption)) (by euclid_assumption "" (show |(a─e)| = |(a─d)|; assumption)) (by euclid_assumption "" (show |(d─f)| = |(a─d)|; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show g.onLine CH; assumption)) (by euclid_assumption "" (show q.onLine CH; assumption)) (by euclid_assumption "" (show b.onLine BL; assumption)) (by euclid_assumption "" (show k.onLine BL; assumption)) (by euclid_assumption "" (show r.onLine BL; assumption)) (by euclid_assumption "" (show g.onLine MN; assumption)) (by euclid_assumption "" (show k.onLine MN; assumption)) (by euclid_assumption "" (show n.onLine MN; assumption)) (by euclid_assumption "" (show q.onLine OP; assumption)) (by euclid_assumption "" (show r.onLine OP; assumption)) (by euclid_assumption "" (show p.onLine OP; assumption)) (by euclid_assumption "" (show n.onLine DF; assumption)) (by euclid_assumption "" (show p.onLine DF; assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(BL.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(MN.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(OP.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AE.intersectsLine DF); assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)) (by euclid_assumption "" (show ∠ a:d:f = ∟; assumption)) (by euclid_assumption "" (show |(b─d)| = |(c─b)|; assumption)) (by euclid_assumption "" (show |(g─k)| = |(k─n)|; assumption)) (by euclid_assumption "" (show |(q─r)| = |(r─p)|; assumption)) (by euclid_assumption "" (show Triangle.area △ g:c:b + Triangle.area △ g:b:k = Triangle.area △ k:b:d + Triangle.area △ k:d:n; assumption)))
  have step7_knrp : formParallelogram k n r p MN OP BL DF := by euclid_apply (helper_2_8_step7_knrp a b c d e f g k n q r p AB AE BL CH DF ED MN OP (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show k.onLine ED; assumption)) (by euclid_assumption "" (show q.onLine ED; assumption)) (by euclid_assumption "" (show |(a─e)| = |(a─d)|; assumption)) (by euclid_assumption "" (show |(d─f)| = |(a─d)|; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show g.onLine CH; assumption)) (by euclid_assumption "" (show q.onLine CH; assumption)) (by euclid_assumption "" (show b.onLine BL; assumption)) (by euclid_assumption "" (show k.onLine BL; assumption)) (by euclid_assumption "" (show r.onLine BL; assumption)) (by euclid_assumption "" (show g.onLine MN; assumption)) (by euclid_assumption "" (show k.onLine MN; assumption)) (by euclid_assumption "" (show n.onLine MN; assumption)) (by euclid_assumption "" (show q.onLine OP; assumption)) (by euclid_assumption "" (show r.onLine OP; assumption)) (by euclid_assumption "" (show p.onLine OP; assumption)) (by euclid_assumption "" (show n.onLine DF; assumption)) (by euclid_assumption "" (show p.onLine DF; assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(BL.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(MN.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(OP.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AE.intersectsLine DF); assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)) (by euclid_assumption "" (show ∠ a:d:f = ∟; assumption)) (by euclid_assumption "" (show |(b─d)| = |(c─b)|; assumption)) (by euclid_assumption "" (show |(g─k)| = |(k─n)|; assumption)) (by euclid_assumption "" (show |(q─r)| = |(r─p)|; assumption)) (by euclid_assumption "" (show Triangle.area △ g:c:b + Triangle.area △ g:b:k = Triangle.area △ k:b:d + Triangle.area △ k:d:n; assumption)))
  euclid_apply (Elements.parallelogram_area' g k q r MN OP CH BL)
  euclid_apply (Elements.parallelogram_area' k n r p MN OP BL DF)
  euclid_apply (Elements.Book1.proposition_36' g q r k k r p n MN OP CH BL BL DF)
  euclid_finish

end Elements.Book2
