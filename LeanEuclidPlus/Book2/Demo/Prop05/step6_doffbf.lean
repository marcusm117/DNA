import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: d ∉ BF. [AFTER: library call.] d on DG; witness b on BF off DG; DG ∦ BF (flipped
   orientation, derived parallel) ⟹ offLine_of_parallel' (x=d carrier DG, w=b target BF). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step6_doffbf (b d : Point) (DG BF : Line)
    (hdDG : d.onLine DG) (hbBF : b.onLine BF)
    (hboffDG : ¬(b.onLine DG))
    (hDGBF : ¬(DG.intersectsLine BF)) :
    ¬(d.onLine BF) :=
  offLine_of_parallel' d b DG BF hdDG hbBF hboffDG hDGBF

end Elements.Book2
