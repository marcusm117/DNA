import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step2 (a f g : Point) (ABC ADE : Circle) (AF AG : Line)
    (left : a.onCircle ABC)
    (left_1 : a.onCircle ADE)
    (left_4 : f.isCentre ABC)
    (left_5 : g.isCentre ADE)
    (haf1 : a.onLine AF) (haf2 : f.onLine AF)
    (hag1 : a.onLine AG) (hag2 : g.onLine AG)
    : distinctPointsOnLine a f AF ∧ distinctPointsOnLine a g AG := by
  constructor <;> refine ⟨?_, ?_, ?_⟩ <;> first | assumption | euclid_finish

end Elements.Book3
