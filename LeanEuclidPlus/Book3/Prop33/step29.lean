import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

-- ∠d:a:e0 = ∟ : AE erected perpendicular to AD at a [Prop 1.11] — directly from the construction.
theorem helper_3_33_step29
    (a d e0 : Point) (hperp : ∠ d:a:e0 = ∟) :
    ∠ d:a:e0 = ∟ := by
  euclid_finish

end Elements.Book3
