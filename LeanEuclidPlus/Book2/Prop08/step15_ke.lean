import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step15_ke (e k q : Point) (ED : Line)
    (h_e_ed : e.onLine ED) (h_k_ed : k.onLine ED)
    (h_kqe : between k q e) :
    distinctPointsOnLine k e ED := by
  euclid_finish

end Elements.Book2
