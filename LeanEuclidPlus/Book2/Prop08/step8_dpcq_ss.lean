import SystemE
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step8_dpcq_ss (c d q : Point) (AB OP : Line)
    (h_c_ab : c.onLine AB) (h_d_ab : d.onLine AB) (h_q_op : q.onLine OP)
    (h_op_ab : ¬(OP.intersectsLine AB)) (h_q_off_ab : ¬(q.onLine AB)) :
    d.sameSide c OP := by
  have h_ab_op : ¬(AB.intersectsLine OP) := by
    intro h
    euclid_apply (intersection_symm AB OP)
    euclid_finish
  have hne_ab_op : AB ≠ OP := fun heq => h_q_off_ab (heq ▸ h_q_op)
  euclid_apply (Elements.sameSide_of_parallel_both d c AB OP)
  euclid_finish

end Elements.Book2
