import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_18_step1 (c d f g : Point) (DE FG : Line)
    (h_gon_DE : g.onLine DE) (h_fon_FG : f.onLine FG) (h_gon_FG : g.onLine FG)
    (h_angle : ∠ c:g:f = ∟ ∨ ∠ d:g:f = ∟) :
    g.onLine DE ∧ f.onLine FG ∧ g.onLine FG ∧ (∠ c:g:f = ∟ ∨ ∠ d:g:f = ∟) := by
  exact ⟨h_gon_DE, h_fon_FG, h_gon_FG, h_angle⟩

end Elements.Book3
