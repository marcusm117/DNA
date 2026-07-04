import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_16_step2 (b e f f' : Point) (BE : Line)
    (h_bef' : between b e f') (h_eff' : between e f f')
    (hassump1 : distinctPointsOnLine b e BE) :
    between b e f := by
  euclid_finish

end Elements.Book1
