import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- AC joins the two distinct points d, b.
theorem helper_3_13_step14 (d b : Point) (AC : Line)
    (hdAC : d.onLine AC) (hbAC : b.onLine AC) (hdb : d ≠ b) :
    distinctPointsOnLine d b AC := by euclid_finish

end Elements.Book3
