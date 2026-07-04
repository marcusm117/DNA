import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_16_h2 (a b c d e : Point) (AB AC : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_a_ne_b : a ≠ b)
    (h_c_AC : c.onLine AC) (h_a_AC : a.onLine AC)
    (h_AC_ne_AB : AC ≠ AB)
    (h_aec : between a e c)
    (h_step13 : ∠ a:c:d > ∠ b:a:e) :
    ∠ a:c:d > ∠ b:a:c := by
  have h_e_AC : e.onLine AC := by
    euclid_apply (between_same_line_in a e c AC); assumption
  have h_eq : ∠ b:a:e = ∠ b:a:c := by
    euclid_apply (equal_angles a b b e c AB AC)
    (try split_ands) <;> euclid_finish
  linarith

end Elements.Book1
