import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- Square AEFD area as two triangles: △aef + △afd = |ad|*|ad|.
   Product-free context (only geometric facts), so euclid_finish can run; the
   lone product lives in the goal, which the SMT translator accepts. -/
set_option systemE.solverTime 30 in
theorem helper_2_8_step27_sq (a b c d e f : Point)
    (AB AE DF EF : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_d_df : d.onLine DF) (h_f_df : f.onLine DF)
    (h_e_ef : e.onLine EF) (h_f_ef : f.onLine EF)
    (h_ae_eq : |(a─e)| = |(a─d)|) (h_df_eq : |(d─f)| = |(a─d)|)
    (h_ae_df : ¬(AE.intersectsLine DF)) (h_ef_ab : ¬(EF.intersectsLine AB))
    (h_dae : ∠ d:a:e = ∟) (h_aef : ∠ a:e:f = ∟) :
    Triangle.area △ a:e:f + Triangle.area △ a:f:d = |(a─d)| * |(a─d)| := by
  have h_e_off_ab : ¬(e.onLine AB) := by
    euclid_apply (Elements.offLine_of_right_angle a d e AB)
    euclid_finish
  have h_d_off_ae : ¬(d.onLine AE) := by
    euclid_apply (Elements.offLine_of_two_points d a e AB AE)
    euclid_finish
  have hne_ae_df : AE ≠ DF := fun heq => h_d_off_ae (heq.symm ▸ h_d_df)
  have h_ae_e : a.sameSide e DF := by
    euclid_apply (Elements.sameSide_of_parallel_both a e AE DF)
    euclid_finish
  have h_sqpar : formParallelogram a d e f AB EF AE DF := by euclid_finish
  euclid_apply (rectangle_area a d e f AB EF AE DF)
  euclid_finish

end Elements.Book2
