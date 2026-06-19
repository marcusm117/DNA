import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: b ∉ EF. [AFTER: library call.] b on AB; witness e on EF off AB (step6_big_eoff);
   EF ∦ AB ⟹ offLine_of_parallel (x=b carrier AB, w=e target EF). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step6_boffef (a b c d e : Point) (AB CE EF : Line)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (heEF : e.onLine EF) (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hacd : between a c d) (hcdb : between c d b)
    (hcelen : |(c─e)| = |(c─b)|) (hbce : ∠ b:c:e = ∟)
    (hEFAB : ¬(EF.intersectsLine AB)) :
    ¬(b.onLine EF) := by
  have step6_big_eoff : ¬(e.onLine AB) := by sorry
  exact offLine_of_parallel b e AB EF hbAB heEF step6_big_eoff hEFAB

end Elements.Book2
