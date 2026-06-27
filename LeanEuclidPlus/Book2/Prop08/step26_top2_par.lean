import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- Top-rest formParallelogram q p h f (q-p on OP, h-f on EF, q-h on CH, p-f on DF).
   Used by step26_top2. Needs OP∥EF (h_efop), CH∥DF (h_chdf). -/
set_option systemE.solverTime 30 in
theorem helper_2_8_step26_top2_par (a b c d e f h q p : Point)
    (AB AE CH DF EF OP ED : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_c_ch : c.onLine CH) (h_h_ch : h.onLine CH) (h_q_ch : q.onLine CH)
    (h_d_df : d.onLine DF) (h_f_df : f.onLine DF) (h_p_df : p.onLine DF)
    (h_h_ef : h.onLine EF) (h_f_ef : f.onLine EF)
    (h_q_op : q.onLine OP) (h_p_op : p.onLine OP)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_ef_ab : ¬(EF.intersectsLine AB)) (h_op_ab : ¬(OP.intersectsLine AB))
    (h_ae_df : ¬(AE.intersectsLine DF)) (h_efop : ¬(EF.intersectsLine OP))
    (h_chdf : ¬(CH.intersectsLine DF)) (h_dae : ∠ d:a:e = ∟) :
    formParallelogram q p h f OP EF CH DF := by
  have h_e_off_ab : ¬(e.onLine AB) := by
    euclid_apply (Elements.offLine_of_right_angle a d e AB)
    euclid_finish
  have h_q_off_ef : ¬(q.onLine EF) := by
    euclid_finish
  have hne_op_ef : OP ≠ EF := fun heq => h_q_off_ef (heq ▸ h_q_op)
  have h_qh_ef : q.sameSide h EF := by
    euclid_apply (Elements.sameSide_of_parallel_both q h CH EF)
    euclid_finish
  euclid_finish

end Elements.Book2
