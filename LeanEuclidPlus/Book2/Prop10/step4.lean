import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step4 (2.10.4): EF is the line through E parallel to AD (proposition_31's outputs).
set_option systemE.solverTime 30 in
theorem helper_2_10_step4
  (e : Point) (EF AD : Line)
  (h1 : e.onLine EF) (h2 : ¬EF.intersectsLine AD) :
  e.onLine EF ∧ ¬(EF.intersectsLine AD) := by
  euclid_finish

end Elements.Book2
