import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_30_step6
    (GK : Line) (a c d k : Point)
    (hk_GK : k.onLine GK)
    (hcside : c.sameSide a GK)
    (hbetw_ckd : between c k d)
    : a.opposingSides d GK := by
  euclid_finish

end Elements.Book1
