import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_15_step11_assumption2_arith_el_sq_lt
    (e l k : Point)
    (h_el_lt_ek : |(e─l)| < |(e─k)|) :
    |(e─l)| * |(e─l)| < |(e─k)| * |(e─k)| := by
  have h_0a := segment_gte_zero (e─l)
  have h_0b := segment_gte_zero (e─k)
  have h_le : |(e─l)| ≤ |(e─k)| := le_of_lt h_el_lt_ek
  have h1 : |(e─l)| * |(e─l)| ≤ |(e─l)| * |(e─k)| :=
    mul_le_mul_of_nonneg_left h_le h_0a
  have h2 : |(e─l)| * |(e─k)| < |(e─k)| * |(e─k)| :=
    mul_lt_mul_of_pos_right h_el_lt_ek (lt_of_le_of_lt h_0a h_el_lt_ek)
  linarith

end Elements.Book3
