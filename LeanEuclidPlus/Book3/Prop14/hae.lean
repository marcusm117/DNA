import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_14_hae
    (a e : Point) (ABDC : Circle)
    (ha : a.onCircle ABDC) (hcen : e.isCentre ABDC) :
    a ≠ e := by euclid_finish

end Elements.Book3
