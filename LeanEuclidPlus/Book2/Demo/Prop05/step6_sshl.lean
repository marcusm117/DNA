import SystemE
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: h and l (both on KM) are on the same side of EF. [AFTER: library call.] witness h
   itself on carrier KM off EF, KM ∦ EF ⟹ sameSide_of_parallel' (carrier-witness sibling, u = h). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step6_sshl (h l : Point) (KM EF : Line)
    (hhKM : h.onLine KM) (hlKM : l.onLine KM)
    (hhoffEF : ¬(h.onLine EF))
    (hKMEF : ¬(KM.intersectsLine EF)) :
    h.sameSide l EF :=
  sameSide_of_parallel' h l h KM EF hhKM hlKM hhKM hhoffEF hKMEF

end Elements.Book2
