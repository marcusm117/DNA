import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_37_step13 (d e f : Point) (ABC : Circle)
    (h4 : ∠ f:e:d = ∟) (h_fe : f ≠ e)
    (h_e_circ : e.onCircle ABC) (h_d_noc : ¬ d.onCircle ABC) :
    ∠ d:e:f = ∟ := by euclid_finish

end Elements.Book3
