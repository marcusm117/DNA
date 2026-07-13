import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_37_step10 (d e b f : Point)
    (h8 : |(d─e)| = |(d─b)|) (h9 : |(f─e)| = |(f─b)|) :
    |(d─e)| = |(d─b)| ∧ |(e─f)| = |(b─f)| := by
  refine ⟨h8, ?_⟩
  rw [segment_symmetric e f, segment_symmetric b f]
  exact h9

end Elements.Book3
