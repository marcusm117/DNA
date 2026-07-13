import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_37_step3 (f e b d : Point) (FE FB FD : Line)
    (h1 : f.onLine FE) (h2 : e.onLine FE) (h3 : f ≠ e)
    (h4 : f.onLine FB) (h5 : b.onLine FB) (h6 : f ≠ b)
    (h7 : f.onLine FD) (h8 : d.onLine FD) (h9 : f ≠ d) :
    distinctPointsOnLine f e FE ∧ distinctPointsOnLine f b FB ∧ distinctPointsOnLine f d FD :=
  ⟨⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩, ⟨h7, h8, h9⟩⟩

end Elements.Book3
