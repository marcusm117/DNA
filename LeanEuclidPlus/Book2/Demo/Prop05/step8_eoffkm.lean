import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.8 sub: ¬(e.onLine KM). [AFTER: library call.] e on EF; h on KM off EF; KM ∦ EF ⟹
   offLine_of_parallel (x=e carrier EF, w=h target KM). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step8_eoffkm (e h : Point) (EF KM : Line)
    (heEF : e.onLine EF) (hhKM : h.onLine KM)
    (hhoffEF : ¬(h.onLine EF))
    (hKMEF : ¬(KM.intersectsLine EF)) :
    ¬(e.onLine KM) :=
  offLine_of_parallel e h EF KM heEF hhKM hhoffEF hKMEF

end Elements.Book2
