import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_2_step3 (d a b e f : Point)
    (h1 : between d a e) (h2 : between d b f) :
    between d a e ∧ between d b f := by
  exact ⟨h1, h2⟩

end Elements.Book1
