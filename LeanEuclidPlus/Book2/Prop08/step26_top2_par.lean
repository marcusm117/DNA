import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- Top-rest formParallelogram q p h f (q-p on OP, h-f on EF, q-h on CH, p-f on DF).
   Used by step26_top2. Needs OP∥EF (h_efop), CH∥DF (h_chdf). -/
theorem helper_2_8_step26_top2_par (a b c d e f m n o h q p : Point)
    (AB AE CH DF EF OP ED : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE) (h_o_ae : o.onLine AE)
    (h_c_ch : c.onLine CH) (h_h_ch : h.onLine CH) (h_q_ch : q.onLine CH)
    (h_d_df : d.onLine DF) (h_f_df : f.onLine DF) (h_p_df : p.onLine DF)
    (h_e_ef : e.onLine EF) (h_h_ef : h.onLine EF) (h_f_ef : f.onLine EF)
    (h_o_op : o.onLine OP) (h_q_op : q.onLine OP) (h_p_op : p.onLine OP)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_moe : between m o e) (h_npf : between n p f)
    (h_q_off_ab : ¬(q.onLine AB))
    (h_ef_ab : ¬(EF.intersectsLine AB)) (h_op_ab : ¬(OP.intersectsLine AB))
    (h_ae_df : ¬(AE.intersectsLine DF)) (h_efop : ¬(EF.intersectsLine OP))
    (h_chdf : ¬(CH.intersectsLine DF)) (h_dae : ∠ d:a:e = ∟) :
    formParallelogram q p h f OP EF CH DF := by
  have h_e_off_ab : ¬(e.onLine AB) := by
    euclid_apply (Elements.offLine_of_right_angle a d e AB)
    euclid_finish
  have h_o_off_ef : ¬(o.onLine EF) := by
    intro h_o_ef
    have h_o_ne_e : o ≠ e := by euclid_finish
    have h_ae_ef : AE = EF := by
      euclid_apply (two_points_determine_line o e AE EF)
      euclid_finish
    have h_a_ef : a.onLine EF := h_ae_ef ▸ h_a_ae
    have hne_ef_ab : EF ≠ AB := fun heq => h_e_off_ab (heq ▸ h_e_ef)
    have h_int : EF.intersectsLine AB := by
      euclid_apply (intersection_lines_common_point a EF AB)
      euclid_finish
    exact h_ef_ab h_int
  have hne_op_ef : OP ≠ EF := fun heq => h_o_off_ef (heq ▸ h_o_op)
  have h_op_ef : ¬(OP.intersectsLine EF) := by
    intro h_int
    have h_sym : EF.intersectsLine OP := by
      euclid_apply (intersection_symm OP EF)
      euclid_finish
    exact h_efop h_sym
  have h_d_off_ch : ¬(d.onLine CH) := by
    euclid_apply (Elements.offLine_of_two_points d c q AB CH)
    euclid_finish
  have hne_ch_df : CH ≠ DF := fun heq => h_d_off_ch (heq ▸ h_d_df)
  have h_qh_df : q.sameSide h DF := by
    euclid_apply (Elements.sameSide_of_parallel_both q h CH DF)
    euclid_finish
  euclid_finish

end Elements.Book2
