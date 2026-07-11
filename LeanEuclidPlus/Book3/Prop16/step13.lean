import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_16_step13
    (a : Point) (ABC : Circle) (AE FA : Line)
    (hFAon : a.onLine FA)
    (hFAne : FA ≠ AE)
    (hFAnot : ¬FA.intersectsCircle ABC)
    : a.onLine FA ∧ FA ≠ AE ∧ ¬FA.intersectsCircle ABC :=
  ⟨hFAon, hFAne, hFAnot⟩

end Elements.Book3
