import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_2_step5 (d g : Point) (GKL : Circle)
    (h1 : d.isCentre GKL) (h2 : g.onCircle GKL) :
    d.isCentre GKL ∧ g.onCircle GKL := by
  exact ⟨h1, h2⟩

end Elements.Book1
