import SystemE
import Helpers.Parallel
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step7_knrp_mnop (a b c d e k q : Point)
    (AB AE BL CH ED MN OP : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d)
    (h_d_ab : d.onLine AB) (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_c_ch : c.onLine CH) (h_q_ch : q.onLine CH)
    (h_b_bl : b.onLine BL) (h_k_bl : k.onLine BL)
    (h_k_mn : k.onLine MN) (h_q_op : q.onLine OP)
    (h_ch_ae : ¬(CH.intersectsLine AE)) (h_bl_ae : ¬(BL.intersectsLine AE))
    (h_mn_ab : ¬(MN.intersectsLine AB)) (h_op_ab : ¬(OP.intersectsLine AB)) (h_dae : ∠ d:a:e = ∟)
    (h_k_off_op : ¬(k.onLine OP)) :
    ¬(MN.intersectsLine OP) := by
  have h_ab_op : ¬(AB.intersectsLine OP) := by
    intro h
    euclid_apply (intersection_symm AB OP)
    euclid_finish
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
  have h_c_ne_d : c ≠ d := by euclid_finish
  have h_c_off_ed : ¬(c.onLine ED) := by
    euclid_apply (Elements.offLine_of_two_points c d e AB ED)
    euclid_finish
  have h_q_off_ab : ¬(q.onLine AB) := by
    intro hq_ab
    have h_c_ne_q : c ≠ q := by
      intro hcq
      exact h_c_off_ed (hcq ▸ h_q_ed)
    have h_ch_ab : CH = AB := by
      euclid_apply (two_points_determine_line c q CH AB)
      euclid_finish
    have hne_ab_ae : AB ≠ AE := fun heq => h_e_off_ab (heq ▸ h_e_ae)
    have hmeet : CH.intersectsLine AE := by
      rw [h_ch_ab]
      euclid_apply (intersection_lines_common_point a AB AE)
      euclid_finish
    exact h_ch_ae hmeet
  have hne_mn_ab : MN ≠ AB := fun heq => h_k_off_ab (heq ▸ h_k_mn)
  have hne_ab_op : AB ≠ OP := fun heq => h_q_off_ab (heq ▸ h_q_op)
  have hne_mn_op : MN ≠ OP := fun heq => h_k_off_op (heq ▸ h_k_mn)
  euclid_apply (Elements.not_intersects_trans MN AB OP)
  euclid_finish

end Elements.Book2
