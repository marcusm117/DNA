import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_1_step2 (a b : Point) (ACE : Circle)
    (hc : b.isCentre ACE) (ha : a.onCircle ACE) :
    b.isCentre ACE ∧ a.onCircle ACE := by
  exact ⟨hc, ha⟩

end Elements.Book1
