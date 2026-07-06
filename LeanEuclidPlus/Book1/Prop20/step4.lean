import SystemE
import Book1Variants.Prop05
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step4 (a b c d d' : Point) (AB BC AC DC : Line)
    (h_aAB : a.onLine AB) (h_bAB : b.onLine AB)
    (h_bBC : b.onLine BC) (h_cBC : c.onLine BC)
    (h_aAC : a.onLine AC) (h_cAC : c.onLine AC)
    (h_AB_ne_BC : AB ≠ BC) (h_BC_ne_AC : BC ≠ AC) (h_AC_ne_AB : AC ≠ AB)
    (h_d'AB : d'.onLine AB) (h_btwn : between a d d')
    (h_dDC : d.onLine DC) (h_cDC : c.onLine DC)
    (hassump1 : |(d─a)| = |(a─c)|) :
    ∠ a:d:c = ∠ a:c:d := by
  have h_dAB : d.onLine AB := between_same_line_in a d d' AB ⟨h_btwn, h_aAB, h_d'AB⟩
  euclid_apply (proposition_5' a c d AC DC AB)
  euclid_finish

end Elements.Book1
