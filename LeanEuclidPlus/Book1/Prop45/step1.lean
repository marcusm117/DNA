import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step1
    (a b d : Point) (AB DB AD : Line)
    (h_b_DB : b.onLine DB)
    (h_d_DB : d.onLine DB)
    (h_a_AB : a.onLine AB)
    (h_b_AB : b.onLine AB)
    (h_a_AD : a.onLine AD)
    (h_d_AD : d.onLine AD)
    (h_AD_AB : AD ≠ AB)
    (h_a_ne_b : a ≠ b) :
    distinctPointsOnLine d b DB := by
  euclid_finish

end Elements.Book1
