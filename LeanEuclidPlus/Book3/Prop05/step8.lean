import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_5_step8 (ABC CDG : Circle) (e c : Point)
    (hne : ABC ≠ CDG)
    (hecABC : e.isCentre ABC) (hecdg : e.isCentre CDG)
    (hcABC : c.onCircle ABC) (hcCDG : c.onCircle CDG)
    : False :=
  hne (equal_circles e c c ABC CDG ⟨hecABC, hecdg, hcABC, hcCDG, rfl⟩)

end Elements.Book3
