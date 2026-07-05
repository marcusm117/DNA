import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_39_step1 (a d : Point) (AD : Line)
    (h1 : a.onLine AD) (h2 : d.onLine AD) (hne : a ≠ d) :
    distinctPointsOnLine a d AD := by
  exact ⟨h1, h2, hne⟩

end Elements.Book1
