import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_20_step1 (a e f : Point) (AEF : Line) (ABC : Circle)
    (h_e_centre : e.isCentre ABC) (h_a_circ : a.onCircle ABC)
    (h_a_AEF : a.onLine AEF) (h_e_AEF : e.onLine AEF)
    (h_f_circ : f.onCircle ABC) (h_f_AEF : f.onLine AEF) (h_bet : between f e a) :
    distinctPointsOnLine a e AEF ∧ f.onCircle ABC ∧ between a e f := by
  euclid_finish

end Elements.Book3
