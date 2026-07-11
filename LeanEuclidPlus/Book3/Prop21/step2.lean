import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_21_step2
    (b f' d : Point) (BF FD : Line) (ABCD : Circle)
    (h_b_BF : b.onLine BF) (h_f'_BF : f'.onLine BF)
    (h_f'_FD : f'.onLine FD) (h_d_FD : d.onLine FD)
    (hctr : f'.isCentre ABCD) (hb : b.onCircle ABCD) (hd : d.onCircle ABCD) :
    distinctPointsOnLine b f' BF ∧ distinctPointsOnLine f' d FD := by
  euclid_finish

end Elements.Book3
