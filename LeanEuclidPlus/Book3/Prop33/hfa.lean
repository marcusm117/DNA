import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

-- f (midpoint of ab) ≠ a, from between a f b.
theorem helper_3_33_hfa
    (a b f : Point) (hafb : between a f b) :
    f ≠ a := by
  euclid_finish

end Elements.Book3
