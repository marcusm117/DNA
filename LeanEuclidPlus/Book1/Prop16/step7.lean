import SystemE
import Book.Prop15
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_16_step7 (a b c e f : Point) (AB BC AC BE : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
    (h_c_AC : c.onLine AC) (h_a_AC : a.onLine AC)
    (h_AB_ne_BC : AB ≠ BC) (h_BC_ne_AC : BC ≠ AC) (h_AC_ne_AB : AC ≠ AB)
    (h_b_BE : b.onLine BE) (h_e_BE : e.onLine BE)
    (h_aec : between a e c)
    (h_bef : between b e f) :
    ∠ a:e:b = ∠ f:e:c := by
  have h_e_AC : e.onLine AC := by
    euclid_apply (between_same_line_in a e c AC)
    assumption
  have h_f_BE : f.onLine BE := by
    euclid_apply (between_same_line_out b e f BE)
    assumption
  have h_feb : between f e b := (between_symm b e f h_bef).1
  have h_BE_ne_AC : BE ≠ AC := by euclid_finish
  have hfull : (∠ a:e:b = ∠ f:e:c) ∧ (∠ b:e:c = ∠ a:e:f) := by
    euclid_apply (proposition_15 a c b f e AC BE)
    (try split_ands) <;> assumption
  exact hfull.1

end Elements.Book1
