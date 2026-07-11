import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_15_step11_assumption2_tri_emn
    (e m n : Point) (ABCD : Circle)
    (ME MN EN : Line)
    (h_centre : e.isCentre ABCD)
    (hm_on : m.onCircle ABCD) (hn_on : n.onCircle ABCD)
    (hm_ME : m.onLine ME) (he_ME : e.onLine ME)
    (he_EN : e.onLine EN) (hn_EN : n.onLine EN)
    (hm_MN : m.onLine MN) (hn_MN : n.onLine MN)
    (h_m_ne_n : m ≠ n)
    (h_e_off_MN : ¬e.onLine MN) :
    formTriangle e m n ME MN EN := by
  euclid_finish

end Elements.Book3
