import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
-- TODO: fill object/hypothesis binders (run --context step15_assumption2)
theorem helper_3_16_step15_assumption2 : ∠ d:a:g < ∟ := by sorry

end Elements.Book3
