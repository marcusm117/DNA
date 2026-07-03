import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_12_hd_ex (c : Point) (AB : Line) (hcAB : ¬c.onLine AB) :
    ∃ d : Point, d.opposingSides c AB := by
  exact exists_point_opposite AB c hcAB

end Elements.Book1
