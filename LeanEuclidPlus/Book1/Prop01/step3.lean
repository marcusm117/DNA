import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_1_step3 (a b c : Point) (CA CB : Line) (BCD ACE : Circle)
    (h1 : c.onLine CA) (h2 : a.onLine CA)
    (h3 : c.onLine CB) (h4 : b.onLine CB)
    (h5 : a.isCentre BCD) (h6 : c.onCircle BCD)
    (h7 : b.isCentre ACE) (h8 : c.onCircle ACE) :
    distinctPointsOnLine c a CA ∧ distinctPointsOnLine c b CB := by
  euclid_finish

end Elements.Book1
