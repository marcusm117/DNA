import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- GB joined: g, b on GB and g ≠ b.
theorem helper_3_33_step6
    (g b : Point) (GB : Line)
    (hgGB : g.onLine GB) (hbGB : b.onLine GB) (hgb : g ≠ b) :
    distinctPointsOnLine g b GB := by
  euclid_finish

end Elements.Book3
