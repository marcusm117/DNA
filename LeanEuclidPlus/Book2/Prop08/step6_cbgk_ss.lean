import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step6_cbgk_ss (a b c d e g : Point) (AB AE BL CH : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d)
    (h_d_ab : d.onLine AB) (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_ae_eq : |(a─e)| = |(a─d)|) (h_c_ch : c.onLine CH) (h_g_ch : g.onLine CH)
    (h_b_bl : b.onLine BL) (h_ch_ae : ¬(CH.intersectsLine AE))
    (h_dae : ∠ d:a:e = ∟) (h_ch_bl : ¬(CH.intersectsLine BL)) :
    c.sameSide g BL := by
  have h_e_off_ab : ¬(e.onLine AB) := by
    euclid_apply (Elements.offLine_of_right_angle a d e AB)
    euclid_finish
  have hne_ab_ae : AB ≠ AE := fun heq => h_e_off_ab (heq ▸ h_e_ae)
  have hne_ch_bl : CH ≠ BL := by
    intro heq
    have hb_ch : b.onLine CH := heq ▸ h_b_bl
    have h_ch_ab : CH = AB := by
      euclid_apply (between_symm a c b)
      euclid_apply (two_points_determine_line c b CH AB)
      euclid_finish
    have hmeet : CH.intersectsLine AE := by
      rw [h_ch_ab]
      euclid_apply (intersection_lines_common_point a AB AE)
      euclid_finish
    exact h_ch_ae hmeet
  euclid_apply (Elements.sameSide_of_parallel_both c g CH BL)
  euclid_finish

end Elements.Book2
