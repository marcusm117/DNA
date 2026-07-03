import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_2_step12 (a l b c g : Point) :
    (|(a─l)| = |(b─g)| ∧ |(b─c)| = |(b─g)|) → |(a─l)| = |(b─c)| := by
  intro h
  obtain ⟨h1, h2⟩ := h
  exact h1.trans h2.symm

end Elements.Book1
