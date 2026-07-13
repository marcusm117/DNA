import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_23_step1 (a b c d : Point) (AB : Line) (ACB ADB : Circle)
    (h_cd : c.sameSide d AB) (h_ne : ACB ≠ ADB) (h_ang : ∠ a:c:b = ∠ a:d:b) :
    c.sameSide d AB ∧ ACB ≠ ADB ∧ ∠ a:c:b = ∠ a:d:b := by
  exact ⟨h_cd, h_ne, h_ang⟩

end Elements.Book3
