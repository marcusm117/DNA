import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_48_step3
    (a b c d d' d'' d''' : Point) (AC AD DC : Line)
    (h_not_d'_AC : ¬d'.onLine AC)
    (h_a_AD : a.onLine AD)
    (h_d'_AD : d'.onLine AD)
    (h_d'''_AD : d'''.onLine AD)
    (h_bet_a_d_d''' : between a d d''')
    (h_da : |(a─d)| = |(a─b)|)
    (h_a_ne_b : a ≠ b)
    (h_c_AC : c.onLine AC)
    (h_a_AC : a.onLine AC)
    (h_d_DC : d.onLine DC)
    (h_c_DC : c.onLine DC)
    : distinctPointsOnLine d c DC := by
  euclid_finish

end Elements.Book1
