import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step9 (2.10.9): "EB and FD will meet" — the application of Post 5 (step8) to our two lines.
-- Sentence 8 states the postulate; sentence 9 is its conclusion for EB, FD: consume step8.
set_option systemE.solverTime 30 in
theorem helper_2_10_step9
  (EB FD : Line)
  (hmeet : EB.intersectsLine FD) :
  EB.intersectsLine FD := hmeet

end Elements.Book2
