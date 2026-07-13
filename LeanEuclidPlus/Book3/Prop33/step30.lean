import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

-- AB bisected at F [Prop 1.10] — the midpoint facts from the construction.
theorem helper_3_33_step30
    (a b f : Point)
    (hafb : between a f b) (haffb : |(a─f)| = |(f─b)|) :
    between a f b ∧ |(a─f)| = |(f─b)| := by
  exact ⟨hafb, haffb⟩

end Elements.Book3
