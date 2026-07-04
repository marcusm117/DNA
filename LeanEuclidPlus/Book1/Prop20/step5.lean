import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_20_step5 (a b c d d' : Point) (AB BC AC DC : Line)
    (h_aAB : a.onLine AB) (h_bAB : b.onLine AB)
    (h_bBC : b.onLine BC) (h_cBC : c.onLine BC)
    (h_aAC : a.onLine AC) (h_cAC : c.onLine AC)
    (h_AB_ne_BC : AB ≠ BC) (h_BC_ne_AC : BC ≠ AC) (h_AC_ne_AB : AC ≠ AB)
    (h_d'AB : d'.onLine AB) (h_btwn_add' : between a d d') (h_btwn_bad : between b a d)
    (h_dDC : d.onLine DC) (h_cDC : c.onLine DC)
    (step4 : ∠ a:d:c = ∠ a:c:d) :
    ∠ b:c:d > ∠ a:d:c := by
  have h_dAB : d.onLine AB := between_same_line_in a d d' AB ⟨h_btwn_add', h_aAB, h_d'AB⟩
  euclid_apply (sum_angles_onlyif c b d a BC DC)
  euclid_finish

end Elements.Book1
