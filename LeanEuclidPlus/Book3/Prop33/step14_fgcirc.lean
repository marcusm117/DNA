import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- FG passes through the centre g of α, so it crosses the circle.
theorem helper_3_33_step14_fgcirc
    (g : Point) (FG : Line) (α : Circle)
    (hgcen : g.isCentre α) (hgFG : g.onLine FG) :
    FG.intersectsCircle α := by
  euclid_finish

end Elements.Book3
