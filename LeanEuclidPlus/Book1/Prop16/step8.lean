import SystemE
import Book.Prop04
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_16_step8 (a b c e f : Point) (AB BC AC BE FC : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_a_ne_b : a ≠ b)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
    (h_c_AC : c.onLine AC) (h_a_AC : a.onLine AC)
    (h_AB_ne_BC : AB ≠ BC) (h_BC_ne_AC : BC ≠ AC) (h_AC_ne_AB : AC ≠ AB)
    (h_b_BE : b.onLine BE) (h_e_BE : e.onLine BE)
    (h_f_FC : f.onLine FC) (h_c_FC : c.onLine FC)
    (h_aec : between a e c) (h_bef : between b e f)
    (h_ae_eq : |(a─e)| = |(e─c)|) (h_be_eq : |(b─e)| = |(e─f)|)
    (h_ang : ∠ a:e:b = ∠ f:e:c) :
    |(a─b)| = |(f─c)| := by
  have h_e_AC : e.onLine AC := by
    euclid_apply (between_same_line_in a e c AC); assumption
  have h_f_BE : f.onLine BE := by
    euclid_apply (between_same_line_out b e f BE); assumption
  have hfull : |(b─a)| = |(f─c)| ∧ (∠ e:b:a = ∠ e:f:c) ∧ (∠ e:a:b = ∠ e:c:f) := by
    euclid_apply (proposition_4 e b a e f c BE AB AC BE FC AC)
    (try split_ands) <;> assumption
  euclid_finish

end Elements.Book1
