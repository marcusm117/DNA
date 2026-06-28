import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step4_cbgk_bnek (a b d e k : Point) (AB AE ED : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_abd : between a b d)
    (h_d_ab : d.onLine AB) (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_ae_eq : |(a─e)| = |(a─d)|) (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED)
    (h_k_ed : k.onLine ED) (h_dae : ∠ d:a:e = ∟) :
    b ≠ k := by
  have h_e_off_ab : ¬(e.onLine AB) := by
    euclid_apply (Elements.offLine_of_right_angle a d e AB)
    euclid_finish
  have h_b_off_ed : ¬(b.onLine ED) := by
    euclid_apply (Elements.offLine_of_two_points b d e AB ED)
    euclid_finish
  intro heq
  exact h_b_off_ed (heq ▸ h_k_ed)

end Elements.Book2
