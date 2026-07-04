import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_20_step3 (a b c d d' : Point) (AB BC DC : Line)
    (h_ab_ne_bc : AB ≠ BC)
    (h_a_on_ab : a.onLine AB) (h_b_on_ab : b.onLine AB)
    (h_b_on_bc : b.onLine BC) (h_c_on_bc : c.onLine BC)
    (h_d'_on_ab : d'.onLine AB) (h_btwn : between a d d')
    (h_step1 : between b a d)
    (h_d_on_dc : d.onLine DC) (h_c_on_dc : c.onLine DC) :
    distinctPointsOnLine d c DC := by
  have h_d_on_ab : d.onLine AB := between_same_line_in a d d' AB ⟨h_btwn, h_a_on_ab, h_d'_on_ab⟩
  euclid_finish

end Elements.Book1
