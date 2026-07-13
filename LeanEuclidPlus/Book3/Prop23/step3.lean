import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_23_step3 (b c d : Point) (AB CB DB : Line)
    (h_bAB : b.onLine AB) (h_cd : c.sameSide d AB)
    (h_cCB : c.onLine CB) (h_bCB : b.onLine CB)
    (h_dDB : d.onLine DB) (h_bDB : b.onLine DB) :
    distinctPointsOnLine c b CB ∧ distinctPointsOnLine d b DB := by
  euclid_finish

end Elements.Book3
