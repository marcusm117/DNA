import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- Mid-rest formParallelogram g n q p (g-n on MN, q-p on OP, g-q on CH, n-p on DF).
   Used by step26_mid2. Needs MN∥OP (h_mnop), CH∥DF (h_chdf). -/
theorem helper_2_8_step26_mid2_par (a b c d e m g n o q p : Point)
    (AB AE CH DF MN OP ED : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE) (h_o_ae : o.onLine AE)
    (h_c_ch : c.onLine CH) (h_g_ch : g.onLine CH) (h_q_ch : q.onLine CH)
    (h_d_df : d.onLine DF) (h_n_df : n.onLine DF) (h_p_df : p.onLine DF)
    (h_m_mn : m.onLine MN) (h_g_mn : g.onLine MN) (h_n_mn : n.onLine MN)
    (h_o_op : o.onLine OP) (h_q_op : q.onLine OP) (h_p_op : p.onLine OP)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_moe : between m o e) (h_npf : between n p f)
    (h_q_off_ab : ¬(q.onLine AB))
    (h_mn_ab : ¬(MN.intersectsLine AB)) (h_op_ab : ¬(OP.intersectsLine AB))
    (h_ae_df : ¬(AE.intersectsLine DF)) (h_mnop : ¬(MN.intersectsLine OP))
    (h_chdf : ¬(CH.intersectsLine DF)) (h_dae : ∠ d:a:e = ∟) :
    formParallelogram g n q p MN OP CH DF := by
  have h_e_off_ab : ¬(e.onLine AB) := by
    euclid_apply (Elements.offLine_of_right_angle a d e AB)
    euclid_finish
  have h_m_off_op : ¬(m.onLine OP) := by
    intro h_m_op
    have h_m_ne_o : m ≠ o := by euclid_finish
    have h_ae_op : AE = OP := by
      euclid_apply (two_points_determine_line m o AE OP)
      euclid_finish
    have h_e_op : e.onLine OP := h_ae_op ▸ h_e_ae
    have hne_op_ab : OP ≠ AB := fun heq => h_e_off_ab (heq ▸ h_e_op)
    have h_int : OP.intersectsLine AB := by
      euclid_apply (intersection_lines_common_point a OP AB)
      euclid_finish
    exact h_op_ab h_int
  have hne_mn_op : MN ≠ OP := fun heq => h_m_off_op (heq ▸ h_m_mn)
  have h_g_off_op : ¬(g.onLine OP) := by
    exact Elements.offLine_of_parallel_simple g MN OP h_g_mn hne_mn_op h_mnop
  have h_gq_df : g.sameSide q DF := by
    have h_d_off_ch : ¬(d.onLine CH) := by
      euclid_apply (Elements.offLine_of_two_points d c q AB CH)
      euclid_finish
    have hne_ch_df : CH ≠ DF := fun heq => h_d_off_ch (heq ▸ h_d_df)
    euclid_apply (Elements.sameSide_of_parallel_both g q CH DF)
    euclid_finish
  euclid_finish

end Elements.Book2
