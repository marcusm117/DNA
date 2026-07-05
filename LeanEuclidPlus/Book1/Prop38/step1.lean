import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_38_step1
  (g h : Point) (AD : Line)
  (hg_AD : g.onLine AD) (hh_AD : h.onLine AD)
  : g.onLine AD ∧ h.onLine AD :=
  ⟨hg_AD, hh_AD⟩

end Elements.Book1
