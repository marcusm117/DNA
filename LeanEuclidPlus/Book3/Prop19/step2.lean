import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_19_step2 (f c : Point) (CF : Line)
    (h_fon : f.onLine CF) (h_con : c.onLine CF) :
    f.onLine CF ∧ c.onLine CF :=
  ⟨h_fon, h_con⟩

end Elements.Book3
