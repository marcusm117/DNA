import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step7_othercases_opp
    (GK : Line) (a c d k : Point)
    (hk_GK : k.onLine GK)
    (hcside : c.sameSide a GK)
    (hbetw_ckd : between c k d)
    : a.opposingSides d GK := by
  euclid_finish

end Elements.Book1
