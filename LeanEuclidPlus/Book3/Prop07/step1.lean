import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_7_step1 (ABCD : Circle) (e b c g : Point) (BE CE GE : Line)
    (h_ctr : e.isCentre ABCD)
    (hb : b.onCircle ABCD) (hc : c.onCircle ABCD) (hg : g.onCircle ABCD)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hgGE : g.onLine GE) (heGE : e.onLine GE)
    : distinctPointsOnLine b e BE ∧ distinctPointsOnLine c e CE ∧ distinctPointsOnLine g e GE := by
  euclid_finish

end Elements.Book3
