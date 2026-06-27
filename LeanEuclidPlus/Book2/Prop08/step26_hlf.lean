import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- between h l f : l = BL ∩ EF lies between h and f on EF. BL separates h (CH side)
   from f (DF side): between c b d, b on BL ⟹ c,d opposite sides of BL; h~c (CH∥BL),
   f~d (DF∥BL). pasch_4 h l f BL EF. -/
set_option systemE.solverTime 30 in
theorem helper_2_8_step26_hlf (a b c d e f h l k q : Point)
    (AB AE CH BL DF EF ED : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_h_ef : h.onLine EF) (h_f_ef : f.onLine EF) (h_l_ef : l.onLine EF)
    (h_f_df : f.onLine DF) (h_d_df : d.onLine DF)
    (h_c_ch : c.onLine CH) (h_h_ch : h.onLine CH)
    (h_l_bl : l.onLine BL) (h_b_bl : b.onLine BL)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_ch_ae : ¬(CH.intersectsLine AE)) (h_bl_ae : ¬(BL.intersectsLine AE))
    (h_ae_df : ¬(AE.intersectsLine DF)) (h_chbl : ¬(CH.intersectsLine BL))
    (h_bldf : ¬(BL.intersectsLine DF)) (h_ef_ab : ¬(EF.intersectsLine AB))
    (h_dae : ∠ d:a:e = ∟) (h_qkd : between q k d) (h_kqe : between k q e) :
    between h l f := by
  have h_hc_bl : h.sameSide c BL := by
    euclid_apply (Elements.sameSide_of_parallel_both h c CH BL)
    euclid_finish
  have h_fd_bl : f.sameSide d BL := by
    euclid_apply (Elements.sameSide_of_parallel_both f d DF BL)
    euclid_finish
  have h_hf_opp : ¬(h.sameSide f BL) := by
    euclid_finish
  euclid_apply (pasch_4 h l f BL EF)
  euclid_finish

end Elements.Book2
