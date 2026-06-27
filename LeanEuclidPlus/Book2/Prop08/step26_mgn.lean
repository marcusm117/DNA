import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- between m g n : g = CH ∩ MN lies between m and n on MN. CH separates m (AE side)
   from n (DF side). Rich context (right-angle anchor h_dae + diagonal ED) so the
   off-line / sameSide facts derive; parallels AE∥CH, DF∥CH supplied as hyps. -/
set_option systemE.solverTime 30 in
theorem helper_2_8_step26_mgn (a b c d e g k m n q : Point)
    (AB AE CH DF MN ED : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE) (h_m_ae : m.onLine AE)
    (h_d_df : d.onLine DF) (h_n_df : n.onLine DF)
    (h_c_ch : c.onLine CH) (h_g_ch : g.onLine CH)
    (h_m_mn : m.onLine MN) (h_g_mn : g.onLine MN) (h_n_mn : n.onLine MN)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_ch_ae : ¬(CH.intersectsLine AE)) (h_ae_df : ¬(AE.intersectsLine DF))
    (h_chdf : ¬(CH.intersectsLine DF)) (h_mn_ab : ¬(MN.intersectsLine AB))
    (h_dae : ∠ d:a:e = ∟) (h_qkd : between q k d) (h_kqe : between k q e) :
    between m g n := by
  have h_mn_opp : ¬(m.sameSide n CH) := by
    euclid_finish
  euclid_apply (pasch_4 m g n CH MN)
  euclid_finish

end Elements.Book2
