import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step15_qhoe_eoffop (d e k q : Point)
    (AB ED OP : Line)
    (h_d_ab : d.onLine AB)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_q_op : q.onLine OP)
    (h_op_ab : ¬(OP.intersectsLine AB))
    (h_kqe : between k q e) (h_op_ne_ab : OP ≠ AB) :
    ¬(e.onLine OP) := by
  intro hon
  euclid_apply (two_points_determine_line e q ED OP)
  euclid_finish

end Elements.Book2
