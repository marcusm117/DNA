import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_5_he_inside_ABC (ABC : Circle) (e : Point)
    (hecABC : e.isCentre ABC)
    : e.insideCircle ABC := by
  euclid_finish

end Elements.Book3
