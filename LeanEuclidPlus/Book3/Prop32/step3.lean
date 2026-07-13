import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_32_step3 (a' d c b : Point) (AD DC CB BD : Line)
    (h_a'_AD : a'.onLine AD) (h_d_AD : d.onLine AD)
    (h_d_DC : d.onLine DC) (h_c_DC : c.onLine DC)
    (h_c_CB : c.onLine CB) (h_b_CB : b.onLine CB)
    (h_d_BD : d.onLine BD) (h_c_off_BD : ¬c.onLine BD) (h_b_BD : b.onLine BD)
    (h_da' : d ≠ a') :
    distinctPointsOnLine a' d AD ∧ distinctPointsOnLine d c DC ∧ distinctPointsOnLine c b CB := by
  euclid_finish

end Elements.Book3
