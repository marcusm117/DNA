import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_5_step9 (ABC CDG : Circle) (e c : Point)
    (hne : ABC ≠ CDG)
    (hcABC : c.onCircle ABC) (hcCDG : c.onCircle CDG)
    : ¬(e.isCentre ABC ∧ e.isCentre CDG) := by
  intro ⟨hecABC, hecdg⟩
  exact hne (equal_circles e c c ABC CDG ⟨hecABC, hecdg, hcABC, hcCDG, rfl⟩)

end Elements.Book3
