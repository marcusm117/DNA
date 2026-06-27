import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- Mid strip formParallelogram m n o p (m-n on MN, o-p on OP, m-o on AE, n-p on DF).
   Used by step26_mid1. Needs MN∥OP (h_mnop), AE∥DF (h_ae_df). -/
set_option systemE.solverTime 30 in
theorem helper_2_8_step26_mid1_par (a b c d e m n o p : Point)
    (AB AE DF MN OP ED : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE) (h_m_ae : m.onLine AE) (h_o_ae : o.onLine AE)
    (h_d_df : d.onLine DF) (h_n_df : n.onLine DF) (h_p_df : p.onLine DF)
    (h_m_mn : m.onLine MN) (h_n_mn : n.onLine MN)
    (h_o_op : o.onLine OP) (h_p_op : p.onLine OP)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_mn_ab : ¬(MN.intersectsLine AB)) (h_op_ab : ¬(OP.intersectsLine AB))
    (h_ae_df : ¬(AE.intersectsLine DF)) (h_mnop : ¬(MN.intersectsLine OP))
    (h_dae : ∠ d:a:e = ∟) :
    formParallelogram m n o p MN OP AE DF := by
  have h_e_off_ab : ¬(e.onLine AB) := by
    euclid_apply (Elements.offLine_of_right_angle a d e AB)
    euclid_finish
  have h_n_off_op : ¬(n.onLine OP) := by
    euclid_finish
  have hne_mn_op : MN ≠ OP := fun heq => h_n_off_op (heq ▸ h_n_mn)
  have h_mo_op : m.sameSide o OP := by
    euclid_apply (Elements.sameSide_of_parallel_both m o AE OP)
    euclid_finish
  euclid_finish

end Elements.Book2
