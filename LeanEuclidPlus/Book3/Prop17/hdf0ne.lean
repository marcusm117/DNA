import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
-- TODO: fill object/hypothesis binders (run --context hdf0ne)
theorem helper_3_17_hdf0ne : d ≠ f0 := by sorry

end Elements.Book3
