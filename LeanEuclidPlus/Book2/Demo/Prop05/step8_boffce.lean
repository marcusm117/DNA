import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.8 sub: ¬(b.onLine CE). [AFTER: library call.] b,c distinct on AB; c on CE; e on CE off AB ⟹
   offLine_of_two_points. b≠c from betweenness (SMT). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step8_boffce (a b c d e : Point) (AB CE EF : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hcCE : c.onLine CE) (heCE : e.onLine CE) (heEF : e.onLine EF)
    (hacd : between a c d) (hcdb : between c d b)
    (heoffAB : ¬(e.onLine AB)) :
    ¬(b.onLine CE) := by
  have hbc : b ≠ c := by euclid_finish
  exact offLine_of_two_points b c e AB CE hbAB hcAB hbc hcCE heCE heoffAB

end Elements.Book2
