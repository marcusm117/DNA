import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step8_dnkb_ss (a b d e k : Point)
    (AB AE BL ED MN : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_abd : between a b d)
    (h_d_ab : d.onLine AB) (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_b_bl : b.onLine BL) (h_k_bl : k.onLine BL) (h_k_mn : k.onLine MN)
    (h_bl_ae : ¬(BL.intersectsLine AE)) (h_dae : ∠ d:a:e = ∟)
    (h_ab_mn : ¬(AB.intersectsLine MN)) :
    d.sameSide b MN := by
  have h_e_off_ab : ¬(e.onLine AB) := by
    euclid_apply (Elements.offLine_of_right_angle a d e AB)
    euclid_finish
  have h_b_off_ed : ¬(b.onLine ED) := by
    euclid_apply (Elements.offLine_of_two_points b d e AB ED)
    euclid_finish
  have h_b_ne_k : b ≠ k := by
    intro hbk
    exact h_b_off_ed (hbk ▸ h_k_ed)
  have h_k_off_ab : ¬(k.onLine AB) := by
    intro hk_ab
    have h_bl_ab : BL = AB := by
      euclid_apply (two_points_determine_line b k BL AB)
      euclid_finish
    have hne_ab_ae : AB ≠ AE := fun heq => h_e_off_ab (heq ▸ h_e_ae)
    have hmeet : BL.intersectsLine AE := by
      rw [h_bl_ab]
      euclid_apply (intersection_lines_common_point a AB AE)
      euclid_finish
    exact h_bl_ae hmeet
  have hne_ab_mn : AB ≠ MN := fun heq => h_k_off_ab (heq ▸ h_k_mn)
  euclid_apply (Elements.sameSide_of_parallel_both d b AB MN)
  euclid_finish

end Elements.Book2
