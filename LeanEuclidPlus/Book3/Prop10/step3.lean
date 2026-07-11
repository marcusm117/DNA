import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_10_step3
    (b k c₀ l m₀ a e : Point) (AC NO : Line)
    (hbkc₀ : ∠ b:k:c₀ = ∟) (haAC : a.onLine AC)
    (hblm₀ : ∠ b:l:m₀ = ∟) (heNO : e.onLine NO)
    : ∠ b:k:c₀ = ∟ ∧ a.onLine AC ∧ ∠ b:l:m₀ = ∟ ∧ e.onLine NO :=
  ⟨hbkc₀, haAC, hblm₀, heNO⟩

end Elements.Book3
