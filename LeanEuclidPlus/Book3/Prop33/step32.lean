import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

-- GB joined: g, b on GB and g ≠ b.
theorem helper_3_33_step32
    (g b : Point) (GB : Line)
    (hgGB : g.onLine GB) (hbGB : b.onLine GB) (hgb : g ≠ b) :
    distinctPointsOnLine g b GB := by
  euclid_finish

end Elements.Book3
