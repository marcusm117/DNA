import SystemE
import Book.Prop47
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_48_step7
    (a b c d d' d'' d''' : Point) (AB BC AC AD DC : Line)
    (h_not_d'_AC : ¬d'.onLine AC)
    (h_d'_angle : ∠d':a:c = ∟)
    (h_a_AD : a.onLine AD)
    (h_d'_AD : d'.onLine AD)
    (h_d''_AD : d''.onLine AD)
    (h_bet_d'_a_d'' : between d' a d'')
    (h_d'''_AD : d'''.onLine AD)
    (h_bet_d''_a_d''' : between d'' a d''')
    (h_ld''' : |(a─d''')| > |(a─b)|)
    (h_bet_a_d_d''' : between a d d''')
    (h_da : |(a─d)| = |(a─b)|)
    (h_a_ne_b : a ≠ b)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
    (h_c_AC : c.onLine AC) (h_a_AC : a.onLine AC)
    (h_AB_ne_BC : AB ≠ BC) (h_BC_ne_AC : BC ≠ AC) (h_AC_ne_AB : AC ≠ AB)
    (h_d_DC : d.onLine DC) (h_c_DC : c.onLine DC)
    (hassump1 : ∠ d:a:c = ∟)
    : |(d─c)| * |(d─c)| = |(d─a)| * |(d─a)| + |(a─c)| * |(a─c)| := by
  have h_d_AD : d.onLine AD := by euclid_finish
  have h_a_ne_c : a ≠ c := by euclid_finish
  have h_AD_ne_DC : AD ≠ DC := by euclid_finish
  euclid_apply (proposition_47 a d c AD DC AC)
  euclid_finish

end Elements.Book1
