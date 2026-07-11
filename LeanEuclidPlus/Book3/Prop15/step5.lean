import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_15_step5
    (m n e f g : Point) (ABCD : Circle) (ME EN FE EG : Line)
    (h_centre : e.isCentre ABCD)
    (hm_on : m.onCircle ABCD)
    (hn_on : n.onCircle ABCD)
    (hf_on : f.onCircle ABCD)
    (hg_on : g.onCircle ABCD)
    (hm_ME : m.onLine ME) (he_ME : e.onLine ME)
    (he_EN : e.onLine EN) (hn_EN : n.onLine EN)
    (hf_FE : f.onLine FE) (he_FE : e.onLine FE)
    (he_EG : e.onLine EG) (hg_EG : g.onLine EG) :
    distinctPointsOnLine m e ME ∧ distinctPointsOnLine e n EN ∧
    distinctPointsOnLine f e FE ∧ distinctPointsOnLine e g EG := by
  euclid_finish

end Elements.Book3
