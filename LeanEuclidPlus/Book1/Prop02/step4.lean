import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_2_step4 (b c : Point) (CGH : Circle)
    (h1 : b.isCentre CGH) (h2 : c.onCircle CGH) :
    b.isCentre CGH ∧ c.onCircle CGH := by
  exact ⟨h1, h2⟩

end Elements.Book1
