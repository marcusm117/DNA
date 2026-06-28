import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step1 (a b c d d' : Point) (AB : Line)
    (h_a_on : a.onLine AB) (h_b_on : b.onLine AB) (h_d'_on : d'.onLine AB)
    (h_abd' : between a b d') (h_bdd' : between b d d')
    (h_bd_eq : |(b─d)| = |(c─b)|) :
    between a b d ∧ |(b─d)| = |(c─b)| := by
  constructor
  · euclid_apply (between_same_line_in b d d' AB)
    euclid_apply (between_symm a b d')
    euclid_apply (between_symm b d d')
    euclid_apply (between_trans_in d' b a d)
    euclid_apply (between_symm d' d a)
    euclid_apply (between_points a b d AB)
    euclid_finish
  · exact h_bd_eq

end Elements.Book2
