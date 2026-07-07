import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_5_step1 (ABC CDG : Circle) (e : Point)
    (hecABC : e.isCentre ABC) (hecdg : e.isCentre CDG)
    : e.isCentre ABC ∧ e.isCentre CDG := by
  exact ⟨hecABC, hecdg⟩

end Elements.Book3
