import SystemE
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: h and g (both on DG) are on the same side of BF. [AFTER: library call.] witness d on
   carrier DG off BF, DG ∦ BF ⟹ sameSide_of_parallel' (carrier-witness sibling). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step6_sshg (d g h : Point) (DG BF : Line)
    (hhDG : h.onLine DG) (hgDG : g.onLine DG) (hdDG : d.onLine DG)
    (hdoffBF : ¬(d.onLine BF))
    (hDGBF : ¬(DG.intersectsLine BF)) :
    h.sameSide g BF :=
  sameSide_of_parallel' h g d DG BF hhDG hgDG hdDG hdoffBF hDGBF

end Elements.Book2
