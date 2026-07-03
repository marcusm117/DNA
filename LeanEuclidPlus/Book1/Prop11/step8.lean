import SystemE
import Book.Prop08
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_11_step8
    (a b c d e f : Point) (AB DF FE FC : Line)
    (hacb : between a c b) (ha : a.onLine AB) (hb : b.onLine AB) (hab : a ≠ b)
    (hdAB : d.onLine AB) (hdc : between c d a) (hce : between c e b)
    (hfd : |(f─d)| = |(d─e)|) (hfe : |(f─e)| = |(d─e)|)
    (hdDF : d.onLine DF) (hfDF : f.onLine DF)
    (hfFE : f.onLine FE) (heFE : e.onLine FE)
    (hfFC : f.onLine FC) (hcFC : c.onLine FC)
    (hDFneAB : DF ≠ AB) (hABneFE : AB ≠ FE) (hFEneDF : FE ≠ DF)
    (hcd_eq_ce : |(c─d)| = |(c─e)|) (hdf_eq_fe : |(d─f)| = |(f─e)|) :
    ∠ d:c:f = ∠ e:c:f := by
  have step8_tri1 : formTriangle c d f AB DF FC := by sorry
  have step8_tri2 : formTriangle c e f AB FE FC := by sorry
  euclid_apply (proposition_8 c d f c e f AB DF FC AB FE FC)
  euclid_finish
