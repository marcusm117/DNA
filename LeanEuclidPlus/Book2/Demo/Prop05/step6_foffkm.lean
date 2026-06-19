import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: f ∉ KM. [AFTER: library call.] f on EF; witness h on KM off EF; KM ∦ EF ⟹
   offLine_of_parallel (x=f carrier EF, w=h target KM). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step6_foffkm (f h : Point) (EF KM : Line)
    (hfEF : f.onLine EF) (hhKM : h.onLine KM)
    (hhoffEF : ¬(h.onLine EF))
    (hKMEF : ¬(KM.intersectsLine EF)) :
    ¬(f.onLine KM) :=
  offLine_of_parallel f h EF KM hfEF hhKM hhoffEF hKMEF

end Elements.Book2
