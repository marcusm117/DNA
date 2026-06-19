import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.8 sub: ¬(c.onLine KM). [AFTER: library call.] c on AB; h on KM off AB; KM ∦ AB ⟹
   offLine_of_parallel (x=c carrier AB, w=h target KM). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step8_coffkm (c h : Point) (AB KM : Line)
    (hcAB : c.onLine AB) (hhKM : h.onLine KM)
    (hhoffAB : ¬(h.onLine AB))
    (hKMAB : ¬(KM.intersectsLine AB)) :
    ¬(c.onLine KM) :=
  offLine_of_parallel c h AB KM hcAB hhKM hhoffAB hKMAB

end Elements.Book2
