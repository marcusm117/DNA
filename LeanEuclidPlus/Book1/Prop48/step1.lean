import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_48_step1
    (a b c d d' d'' d''' : Point) (AB BC AC AD : Line)
    (h_not_d'_AC : ¬d'.onLine AC)
    (h_d'_angle : ∠d':a:c = ∟)
    (h_a_AD : a.onLine AD)
    (h_d'_AD : d'.onLine AD)
    (h_d''_AD : d''.onLine AD)
    (h_bet_d'_a_d'' : between d' a d'')
    (h_d'''_AD : d'''.onLine AD)
    (h_bet_d''_a_d''' : between d'' a d''')
    (h_bet_a_d_d''' : between a d d''')
    (h_da : |(a─d)| = |(a─b)|)
    (h_a_ne_b : a ≠ b)
    (h_a_AB : a.onLine AB)
    (h_b_AB : b.onLine AB)
    (h_b_BC : b.onLine BC)
    (h_c_BC : c.onLine BC)
    (h_AB_ne_BC : AB ≠ BC)
    (h_c_AC : c.onLine AC)
    (h_a_AC : a.onLine AC)
    : ∠ d:a:c = ∟ := by
  have h_d_AD : d.onLine AD := by euclid_finish
  have h_a_ne_c : a ≠ c := by euclid_finish
  have h_not_bet_d_a_d' : ¬between d a d' := by euclid_finish
  euclid_apply (equal_angles a d d' c c AD AC)
  linarith

end Elements.Book1
