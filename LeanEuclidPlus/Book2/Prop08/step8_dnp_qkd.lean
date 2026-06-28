import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step8_dnp_qkd (a b c d e k q : Point) (AB AE BL ED : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d)
    (h_d_ab : d.onLine AB) (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_b_bl : b.onLine BL) (h_k_bl : k.onLine BL)
    (h_dae : ∠ d:a:e = ∟) (h_dq : distinctPointsOnLine d q ED)
    (h_qcbl : q.sameSide c BL) :
    between q k d := by
  have h_e_off_ab : ¬(e.onLine AB) := by
    euclid_apply (Elements.offLine_of_right_angle a d e AB)
    euclid_finish
  have h_b_off_ed : ¬(b.onLine ED) := by
    euclid_apply (Elements.offLine_of_two_points b d e AB ED)
    euclid_finish
  have hne_bl_ed : BL ≠ ED := fun heq => h_b_off_ed (heq ▸ h_b_bl)
  have h_cbd : between c b d := by
    euclid_finish
  euclid_apply (pasch_3 c b d BL)
  euclid_apply (pasch_4 q k d BL ED)
  euclid_finish

end Elements.Book2
