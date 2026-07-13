import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step1 (ABC : Circle) (DA : Line) :
    (∃ f : Point, f.isCentre ABC ∧ f.onLine DA) ∨
             ¬(∃ f : Point, f.isCentre ABC ∧ f.onLine DA) :=
  Classical.em _

end Elements.Book3
