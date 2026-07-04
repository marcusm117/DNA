import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step1 (b a d d' : Point) (AB : Line)
    (h_b_on : b.onLine AB) (h_a_on : a.onLine AB) (h_d'_on : d'.onLine AB)
    (hbad' : between b a d') (hadd' : between a d d') :
    between b a d := by
  euclid_apply (between_same_line_in a d d' AB)
  euclid_apply (between_symm b a d')
  euclid_apply (between_symm a d d')
  euclid_apply (between_trans_in d' a b d)
  euclid_apply (between_symm d' d b)
  euclid_apply (between_points b a d AB)
  euclid_finish

end Elements.Book1
