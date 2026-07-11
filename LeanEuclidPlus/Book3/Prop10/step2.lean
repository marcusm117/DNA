import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_10_step2
    (b h k g l : Point)
    (hbkh : between b k h) (hbkh' : |(b─k)| = |(k─h)|)
    (hblg : between b l g) (hblg' : |(b─l)| = |(l─g)|)
    : between b k h ∧ |(b─k)| = |(k─h)| ∧ between b l g ∧ |(b─l)| = |(l─g)| :=
  ⟨hbkh, hbkh', hblg, hblg'⟩

end Elements.Book3
