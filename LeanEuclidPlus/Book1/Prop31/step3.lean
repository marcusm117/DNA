import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_31_step3 (a d e c : Point) (AD BC : Line)
    (hane : e ≠ a) (had : a ≠ d) (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hdBC : d.onLine BC) (hcBC : c.onLine BC)
    (hangle : ∠ e:a:d = ∠ a:d:c) : ∠ d:a:e = ∠ a:d:c := by
  euclid_finish

end Elements.Book1
