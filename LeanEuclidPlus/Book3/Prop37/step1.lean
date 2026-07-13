import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_37_step1 (d e : Point) (ABC : Circle) (DE : Line)
    (h1 : d.onLine DE) (h2 : e.onLine DE) (h3 : e.onCircle ABC) (h4 : ¬ DE.intersectsCircle ABC) :
    d.onLine DE ∧ e.onLine DE ∧ e.onCircle ABC ∧ ¬ DE.intersectsCircle ABC :=
  ⟨h1, h2, h3, h4⟩

end Elements.Book3
