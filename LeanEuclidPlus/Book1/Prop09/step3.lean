import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_9_step3 (a b c d e : Point) (AB AC DE : Line)
    (h1 : AB ≠ AC)
    (h2 : a.onLine AB) (h3 : d.onLine AB)
    (h4 : a.onLine AC) (h5 : c.onLine AC)
    (h6 : between a d b) (h7 : between a e c)
    (h8 : d.onLine DE) (h9 : e.onLine DE) :
    distinctPointsOnLine d e DE := by euclid_finish

end Elements.Book1
