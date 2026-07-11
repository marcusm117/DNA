import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_14_hec
    (c e : Point) (ABDC : Circle)
    (hc : c.onCircle ABDC) (hcen : e.isCentre ABDC) :
    e ≠ c := by euclid_finish

end Elements.Book3
