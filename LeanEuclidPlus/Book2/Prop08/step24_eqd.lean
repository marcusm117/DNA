import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step24_eqd (d e k q : Point) (ED : Line)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_qkd : between q k d) (h_kqe : between k q e) :
    between e q d := by
  euclid_finish

end Elements.Book2
