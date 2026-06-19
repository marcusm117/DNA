import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: h ∉ BF. [AFTER: library call.] h on DG; witness b on BF off DG; DG ∦ BF (flipped
   orientation) ⟹ offLine_of_parallel' (x=h carrier DG, w=b target BF). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step6_hoffbf (b h : Point) (DG BF : Line)
    (hhDG : h.onLine DG) (hbBF : b.onLine BF)
    (hboffDG : ¬(b.onLine DG))
    (hDGBF : ¬(DG.intersectsLine BF)) :
    ¬(h.onLine BF) :=
  offLine_of_parallel' h b DG BF hhDG hbBF hboffDG hDGBF

end Elements.Book2
