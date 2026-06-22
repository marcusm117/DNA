import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step6_bdkn_ss (a b d e f k : Point) (AB AE BL DF : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_abd : between a b d)
    (h_d_ab : d.onLine AB) (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_d_df : d.onLine DF) (h_f_df : f.onLine DF)
    (h_ae_eq : |(a─e)| = |(a─d)|) (h_df_eq : |(d─f)| = |(a─d)|)
    (h_b_bl : b.onLine BL) (h_k_bl : k.onLine BL)
    (h_dae : ∠ d:a:e = ∟) (h_adf : ∠ a:d:f = ∟)
    (h_bl_df : ¬(BL.intersectsLine DF)) :
    b.sameSide k DF := by
  have h_f_off_ab : ¬(f.onLine AB) := by
    euclid_apply (Elements.offLine_of_right_angle d a f AB)
    euclid_finish
  have h_b_off_df : ¬(b.onLine DF) := by
    euclid_apply (Elements.offLine_of_two_points b d f AB DF)
    euclid_finish
  have hne_bl_df : BL ≠ DF := fun heq => h_b_off_df (heq ▸ h_b_bl)
  euclid_apply (Elements.sameSide_of_parallel_both b k BL DF)
  euclid_finish

end Elements.Book2
