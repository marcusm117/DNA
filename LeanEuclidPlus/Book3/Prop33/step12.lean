import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- EB joined: e, b on EB and e ≠ b.
theorem helper_3_33_step12
    (e b : Point) (EB : Line)
    (heEB : e.onLine EB) (hbEB : b.onLine EB) (heb : e ≠ b) :
    distinctPointsOnLine e b EB := by
  euclid_finish

end Elements.Book3
