import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_14_step3
    (a c e : Point) (AE EC : Line)
    (haAE : a.onLine AE) (heAE : e.onLine AE) (hae : a ≠ e)
    (heEC : e.onLine EC) (hcEC : c.onLine EC) (hec : e ≠ c) :
    distinctPointsOnLine a e AE ∧ distinctPointsOnLine e c EC := by
  euclid_finish

end Elements.Book3
