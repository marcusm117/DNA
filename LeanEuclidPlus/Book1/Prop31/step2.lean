import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_31_step2 (a d : Point) (BC AD : Line)
    (haoff : ¬a.onLine BC) (hdon : d.onLine BC)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) : distinctPointsOnLine a d AD := by
  euclid_finish

end Elements.Book1
