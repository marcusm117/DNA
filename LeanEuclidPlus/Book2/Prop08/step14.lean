import SystemE
import Book.Prop36
import Helpers.Area
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step14 (a b c d e f g k h l m n o q r p : Point)
    (AB AE BL CH DF ED EF MN OP : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_d_df : d.onLine DF) (h_f_df : f.onLine DF)
    (h_e_ef : e.onLine EF) (h_f_ef : f.onLine EF)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|) (h_df_eq : |(d─f)| = |(a─d)|)
    (h_c_ch : c.onLine CH) (h_g_ch : g.onLine CH) (h_q_ch : q.onLine CH) (h_h_ch : h.onLine CH)
    (h_b_bl : b.onLine BL) (h_k_bl : k.onLine BL) (h_r_bl : r.onLine BL) (h_l_bl : l.onLine BL)
    (h_g_mn : g.onLine MN) (h_k_mn : k.onLine MN)
    (h_q_op : q.onLine OP) (h_r_op : r.onLine OP) (h_p_op : p.onLine OP)
    (h_h_ef : h.onLine EF) (h_l_ef : l.onLine EF)
    (h_p_df : p.onLine DF)
    (h_ch_ae : ¬(CH.intersectsLine AE)) (h_bl_ae : ¬(BL.intersectsLine AE))
    (h_mn_ab : ¬(MN.intersectsLine AB)) (h_op_ab : ¬(OP.intersectsLine AB))
    (h_ae_df : ¬(AE.intersectsLine DF)) (h_ef_ab : ¬(EF.intersectsLine AB))
    (h_dae : ∠ d:a:e = ∟) (h_adf : ∠ a:d:f = ∟)
    (h_qr_rp : |(q─r)| = |(r─p)|) :
    Triangle.area △ q:r:l + Triangle.area △ q:l:h =
      Triangle.area △ r:p:f + Triangle.area △ r:f:l := by
  have step12_gkgq_ang_qkd : between q k d := by sorry
  have step7_gkqr_chbl : ¬(CH.intersectsLine BL) := by sorry
  have step7_knrp_bldf : ¬(BL.intersectsLine DF) := by sorry
  have step14_efop : ¬(EF.intersectsLine OP) := by sorry
  have h_e_off_ab : ¬(e.onLine AB) := by
    euclid_apply (Elements.offLine_of_right_angle a d e AB)
    euclid_finish
  have hne_ef_ab : EF ≠ AB := fun heq => h_e_off_ab (heq ▸ h_e_ef)
  have h_q_off_ef : ¬(q.onLine EF) := by
    euclid_finish
  have hne_ef_op : EF ≠ OP := fun heq => h_q_off_ef (heq ▸ h_q_op)
  have step14_hqbl : h.sameSide q BL := by sorry
  have step14_lrdf : l.sameSide r DF := by sorry
  have step14_hlqr : formParallelogram h l q r EF OP CH BL := by sorry
  have step14_lfrp : formParallelogram l f r p EF OP BL DF := by sorry
  euclid_apply (Elements.parallelogram_area' h l q r EF OP CH BL)
  euclid_apply (Elements.parallelogram_area' l f r p EF OP BL DF)
  euclid_apply (Elements.Book1.proposition_36' h q r l l r p f EF OP CH BL BL DF)
  euclid_finish

end Elements.Book2
