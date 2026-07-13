import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

-- b is on circle α (centre f, radius fa): since f is the midpoint, |(f─b)| = |(f─a)| = radius.
theorem helper_3_33_hb_circ_2
    (a b f : Point) (α : Circle)
    (hfcen : f.isCentre α) (hacirc : a.onCircle α) (haffb : |(a─f)| = |(f─b)|) :
    b.onCircle α := by
  euclid_finish

end Elements.Book3
