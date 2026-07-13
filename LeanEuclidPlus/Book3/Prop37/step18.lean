import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_37_step18 (d f c b : Point) (ABC : Circle) (DB : Line)
    (h17 : (∃ p : Point, p.onLine DB ∧ p.onCircle ABC) ∧ ¬ DB.intersectsCircle ABC) :
    collinear d f c →
        (∃ p : Point, p.onLine DB ∧ p.onCircle ABC) ∧ ¬ DB.intersectsCircle ABC :=
  fun _ => h17

end Elements.Book3
