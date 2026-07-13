import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_34_step1 (b : Point) (ABC : Circle) (EF : Line)
    (hb_EF : b.onLine EF) (hb_ABC : b.onCircle ABC) (hEF_notint : ¬ EF.intersectsCircle ABC) :
    b.onLine EF ∧ b.onCircle ABC ∧ ¬ EF.intersectsCircle ABC :=
  ⟨hb_EF, hb_ABC, hEF_notint⟩

end Elements.Book3
