import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_7_step10
    (ABCD : Circle) (a d e f g : Point) (AD GE : Line)
    (h_ctr : e.isCentre ABCD)
    (ha : a.onCircle ABCD) (hd : d.onCircle ABCD) (hg : g.onCircle ABCD)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hbet_aed : between a e d) (hbet_efd : between e f d)
    (hgGE : g.onLine GE) (heGE : e.onLine GE)
    (h_gne_a : g ≠ a) (h_gne_d : g ≠ d)
    (hassump1 : |(g─f)| + |(f─e)| > |(g─e)|)
    (hassump2 : |(e─g)| = |(e─d)|)
    : |(g─f)| + |(f─e)| > |(e─d)| := by
  have step10_assumption1 : |(g─f)| + |(f─e)| > |(g─e)| := by sorry
  linarith [segment_symmetric g e]

end Elements.Book3
