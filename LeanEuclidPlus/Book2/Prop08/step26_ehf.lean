import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- between e h f : h = CH ∩ EF lies between e and f on EF. CH separates e (AE side)
   from f (DF side): between a c d, c on CH ⟹ a,d opposite sides of CH; e~a (AE∥CH),
   f~d (DF∥CH). pasch_4 e h f CH EF. -/
theorem helper_2_8_step26_ehf (a b c d e f h k q : Point)
    (AB AE CH DF EF ED : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_e_ef : e.onLine EF) (h_f_ef : f.onLine EF) (h_h_ef : h.onLine EF)
    (h_d_df : d.onLine DF) (h_f_df : f.onLine DF)
    (h_c_ch : c.onLine CH) (h_h_ch : h.onLine CH)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_ch_ae : ¬(CH.intersectsLine AE)) (h_ae_df : ¬(AE.intersectsLine DF))
    (h_chdf : ¬(CH.intersectsLine DF)) (h_ef_ab : ¬(EF.intersectsLine AB))
    (h_dae : ∠ d:a:e = ∟) (h_qkd : between q k d) (h_kqe : between k q e) :
    between e h f := by
  have h_ef_opp : ¬(e.sameSide f CH) := by
    euclid_finish
  euclid_apply (pasch_4 e h f CH EF)
  euclid_finish

end Elements.Book2
