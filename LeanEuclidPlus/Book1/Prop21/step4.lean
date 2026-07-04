import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_21_step4 (a b c d e : Point) (AB BC AC BD : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD) (heBD : e.onLine BD) (heAC : e.onLine AC)
    (hbdAC : b.sameSide d AC) (hadBC : a.sameSide d BC) (hcdAB : c.sameSide d AB)
    (hstep1 : between b d e ∧ e.onLine BD)
    (hstep3 : |(a─b)| + |(a─e)| + |(e─c)| > |(b─e)| + |(e─c)|) :
    |(b─a)| + |(a─c)| > |(b─e)| + |(e─c)| := by
  have hbet : between a e c := by euclid_finish
  have hba_sym : |(b─a)| = |(a─b)| := segment_symmetric b a
  linarith [between_if a e c hbet]

end Elements.Book1
