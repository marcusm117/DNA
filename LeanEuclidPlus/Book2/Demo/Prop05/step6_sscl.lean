import SystemE
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: c and l (both on CE) are on the same side of DG. [AFTER: library call.] witness d on DG
   off CE, CE ∦ DG ⟹ sameSide_of_parallel. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step6_sscl (c d l : Point) (CE DG : Line)
    (hcCE : c.onLine CE) (hlCE : l.onLine CE) (hdDG : d.onLine DG)
    (hdoffCE : ¬(d.onLine CE))
    (hDGCE : ¬(DG.intersectsLine CE)) :
    c.sameSide l DG :=
  sameSide_of_parallel c l d CE DG hcCE hlCE hdDG hdoffCE hDGCE

end Elements.Book2
