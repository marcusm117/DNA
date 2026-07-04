import SystemE
import Book.Prop08
import Book1.Prop11.step8_tri1
import Book1.Prop11.step8_tri2
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

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
  have step8_tri1 : formTriangle c d f AB DF FC := by euclid_apply (helper_1_11_step8_tri1 a b c d e f AB DF FC (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between c d a; assumption)) (by euclid_assumption "" (show between c e b; assumption)) (by euclid_assumption "" (show |(f─d)| = |(d─e)|; assumption)) (by euclid_assumption "" (show |(f─e)| = |(d─e)|; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine FC; assumption)) (by euclid_assumption "" (show c.onLine FC; assumption)) (by euclid_assumption "" (show DF ≠ AB; assumption)))
  have step8_tri2 : formTriangle c e f AB FE FC := by euclid_apply (helper_1_11_step8_tri2 a b c d e f AB FE FC (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between c d a; assumption)) (by euclid_assumption "" (show between c e b; assumption)) (by euclid_assumption "" (show |(f─d)| = |(d─e)|; assumption)) (by euclid_assumption "" (show |(f─e)| = |(d─e)|; assumption)) (by euclid_assumption "" (show f.onLine FE; assumption)) (by euclid_assumption "" (show e.onLine FE; assumption)) (by euclid_assumption "" (show f.onLine FC; assumption)) (by euclid_assumption "" (show c.onLine FC; assumption)) (by euclid_assumption "" (show AB ≠ FE; assumption)))
  euclid_apply (proposition_8 c d f c e f AB DF FC AB FE FC)
  euclid_finish
