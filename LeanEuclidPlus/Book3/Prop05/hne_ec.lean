import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_5_hne_ec (ABC : Circle) (e c : Point)
    (hecABC : e.isCentre ABC) (hcABC : c.onCircle ABC)
    : e ≠ c := by
  euclid_finish

end Elements.Book3
