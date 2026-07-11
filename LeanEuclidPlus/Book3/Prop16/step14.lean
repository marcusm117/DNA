import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_16_step14
    (a g d : Point) (FA : Line)
    (hgFA : g.onLine FA)
    (hgperp : ∠ a:g:d = ∟)
    : g.onLine FA ∧ ∠ a:g:d = ∟ := ⟨hgFA, hgperp⟩

end Elements.Book3
