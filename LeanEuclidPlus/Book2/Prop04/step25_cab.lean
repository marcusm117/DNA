import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.25 sub: c.onLine AB (c is between a and b on AB). -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step25_cab (a b c : Point) (AB : Line)
    (hacb : between a c b) (haAB : a.onLine AB) (hbAB : b.onLine AB) :
    c.onLine AB := by
  euclid_apply (between_same_line_in a c b AB)
  euclid_finish

end Elements.Book2
