import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step5_bdrp_dnep (a b c d e q p : Point)
    (AB AE CH ED OP : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d)
    (h_d_ab : d.onLine AB) (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|) (h_c_ch : c.onLine CH) (h_q_ch : q.onLine CH)
    (h_q_op : q.onLine OP) (h_p_op : p.onLine OP)
    (h_ch_ae : ¬(CH.intersectsLine AE)) (h_ab_op : ¬(AB.intersectsLine OP))
    (h_dae : ∠ d:a:e = ∟) :
    d ≠ p := by
  have h_e_off_ab : ¬(e.onLine AB) := by
    euclid_apply (Elements.offLine_of_right_angle a d e AB)
    euclid_finish
  have h_c_ne_d : c ≠ d := by
    euclid_finish
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
  have hne_ab_op : AB ≠ OP := fun heq => h_q_off_ab (heq ▸ h_q_op)
  have h_d_off_op : ¬(d.onLine OP) := by
    euclid_apply (Elements.offLine_of_parallel_simple d AB OP)
    euclid_finish
  intro hdp
  exact h_d_off_op (hdp ▸ h_p_op)

end Elements.Book2
