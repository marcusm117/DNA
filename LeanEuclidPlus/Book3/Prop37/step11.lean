import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_37_step11 (f d : Point) (FD : Line)
    (h1 : f.onLine FD) (h2 : d.onLine FD) (h3 : f ≠ d) :
    distinctPointsOnLine f d FD := ⟨h1, h2, h3⟩

end Elements.Book3
