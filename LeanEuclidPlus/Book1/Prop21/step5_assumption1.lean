import SystemE
import Book1.Prop20.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_21_step5_assumption1 (a b c d e : Point) (AB BC AC BD DC : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD) (heBD : e.onLine BD) (heAC : e.onLine AC)
    (hdDC : d.onLine DC) (hcDC : c.onLine DC)
    (hbdAC : b.sameSide d AC) (hadBC : a.sameSide d BC) (hcdAB : c.sameSide d AB) :
    |(c─e)| + |(e─d)| > |(c─d)| := by
  euclid_apply (proposition_20 e c d AC DC BD)
  euclid_finish

end Elements.Book1
