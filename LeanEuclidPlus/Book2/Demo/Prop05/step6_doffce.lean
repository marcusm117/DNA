import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: d ∉ CE. [AFTER: library call.] d,c distinct on AB; c on CE; e on CE off AB
   (step6_big_eoff) ⟹ offLine_of_two_points. The d≠c is derived from between a c d (SMT). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step6_doffce (a b c d e : Point) (AB CE : Line)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hacd : between a c d) (hcdb : between c d b)
    (hcelen : |(c─e)| = |(c─b)|) (hbce : ∠ b:c:e = ∟) :
    ¬(d.onLine CE) := by
  have step6_big_eoff : ¬(e.onLine AB) := by sorry
  have hdc : d ≠ c := by euclid_finish
  exact offLine_of_two_points d c e AB CE hdAB hcAB hdc hcCE heCE step6_big_eoff

end Elements.Book2
