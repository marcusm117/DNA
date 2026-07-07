import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_3_step1
    (a b e e' : Point) (ABC : Circle) (AB EA EB : Line)
    (he : e.isCentre ABC) (heAB : ¬e.onLine AB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (he' : e'.isCentre ABC)
    (heEA : e.onLine EA) (haEA : a.onLine EA)
    (heEB : e.onLine EB) (hbEB : b.onLine EB)
    : e'.isCentre ABC ∧ e' = e ∧ distinctPointsOnLine e a EA ∧ distinctPointsOnLine e b EB := by
  have heqe : e' = e := by euclid_finish
  subst heqe
  exact ⟨he, rfl, by euclid_finish, by euclid_finish⟩

end Elements.Book3
