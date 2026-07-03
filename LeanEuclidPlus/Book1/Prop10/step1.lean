import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_10_step1 (a b c : Point) (AB AC BC : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hca : |(c─a)| = |(a─b)|) (hcb : |(c─b)| = |(a─b)|)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hcBC : c.onLine BC) (hbBC : b.onLine BC) :
    formTriangle a b c AB BC AC ∧ |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)| := by
  euclid_finish

end Elements.Book1
