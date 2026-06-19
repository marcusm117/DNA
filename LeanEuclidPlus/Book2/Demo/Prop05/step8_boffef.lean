import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.8 sub: ¬(b.onLine EF). [AFTER: library call.] b on AB; e on EF off AB; EF ∦ AB ⟹
   offLine_of_parallel (x=b carrier AB, w=e target EF). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step8_boffef (b e : Point) (AB EF : Line)
    (hbAB : b.onLine AB) (heEF : e.onLine EF)
    (heoffAB : ¬(e.onLine AB))
    (hEFAB : ¬(EF.intersectsLine AB)) :
    ¬(b.onLine EF) :=
  offLine_of_parallel b e AB EF hbAB heEF heoffAB hEFAB

end Elements.Book2
