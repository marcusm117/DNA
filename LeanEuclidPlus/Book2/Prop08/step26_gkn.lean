import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- between g k n : k = BL ∩ MN lies between g and n on MN. BL separates g (CH side)
   from n (DF side): between c b d with b on BL ⟹ c,d opposite sides of BL; g~c
   (CH∥BL), n~d (DF∥BL). pasch_4 g k n BL MN. -/
set_option systemE.solverTime 30 in
theorem helper_2_8_step26_gkn (a b c d e g k n q : Point)
    (AB AE CH BL DF MN ED : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_g_ch : g.onLine CH) (h_c_ch : c.onLine CH)
    (h_k_bl : k.onLine BL) (h_b_bl : b.onLine BL)
    (h_n_df : n.onLine DF) (h_d_df : d.onLine DF)
    (h_g_mn : g.onLine MN) (h_k_mn : k.onLine MN) (h_n_mn : n.onLine MN)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_ch_ae : ¬(CH.intersectsLine AE)) (h_bl_ae : ¬(BL.intersectsLine AE))
    (h_ae_df : ¬(AE.intersectsLine DF)) (h_chbl : ¬(CH.intersectsLine BL))
    (h_bldf : ¬(BL.intersectsLine DF)) (h_mn_ab : ¬(MN.intersectsLine AB))
    (h_dae : ∠ d:a:e = ∟) (h_qkd : between q k d) (h_kqe : between k q e) :
    between g k n := by
  have h_gc_bl : g.sameSide c BL := by
    euclid_apply (Elements.sameSide_of_parallel_both g c CH BL)
    euclid_finish
  have h_nd_bl : n.sameSide d BL := by
    euclid_apply (Elements.sameSide_of_parallel_both n d DF BL)
    euclid_finish
  have h_gn_opp : ¬(g.sameSide n BL) := by
    euclid_finish
  euclid_apply (pasch_4 g k n BL MN)
  euclid_finish

end Elements.Book2
