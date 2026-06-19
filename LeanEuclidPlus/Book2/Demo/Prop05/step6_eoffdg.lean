import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: e ∉ DG. [AFTER: library call.] e on CE; witness d on DG off CE; DG ∦ CE ⟹
   offLine_of_parallel (x=e carrier CE, w=d target DG). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step6_eoffdg (d e : Point) (CE DG : Line)
    (heCE : e.onLine CE) (hdDG : d.onLine DG)
    (hdoffCE : ¬(d.onLine CE))
    (hDGCE : ¬(DG.intersectsLine CE)) :
    ¬(e.onLine DG) :=
  offLine_of_parallel e d CE DG heCE hdDG hdoffCE hDGCE

end Elements.Book2
