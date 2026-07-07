import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_5_hne_eg (CDG : Circle) (e g : Point)
    (hecdg : e.isCentre CDG) (hgCDG : g.onCircle CDG)
    : e ≠ g := by
  euclid_finish

end Elements.Book3
