import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_34_step3_assumption2 (b c : Point) (ABC : Circle) (BC : Line)
    (hb_ABC : b.onCircle ABC) (hb_BC : b.onLine BC) (hc_ABC : c.onCircle ABC)
    (hc_BC : c.onLine BC) (hbc_ne : b ≠ c) :
    b.onCircle ABC ∧ b.onLine BC ∧ c.onCircle ABC ∧ c.onLine BC ∧ b ≠ c :=
  ⟨hb_ABC, hb_BC, hc_ABC, hc_BC, hbc_ne⟩

end Elements.Book3
