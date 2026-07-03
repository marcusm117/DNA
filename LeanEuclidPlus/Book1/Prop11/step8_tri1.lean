import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_11_step8_tri1
    (a b c d e f : Point) (AB DF FC : Line)
    (hacb : between a c b) (ha : a.onLine AB) (hb : b.onLine AB) (hab : a ≠ b)
    (hdAB : d.onLine AB) (hdc : between c d a) (hce : between c e b)
    (hfd : |(f─d)| = |(d─e)|) (hfe : |(f─e)| = |(d─e)|)
    (hdDF : d.onLine DF) (hfDF : f.onLine DF)
    (hfFC : f.onLine FC) (hcFC : c.onLine FC)
    (hDFneAB : DF ≠ AB) :
    formTriangle c d f AB DF FC := by
  refine ⟨⟨?_, hdAB, ?_⟩, hdDF, hfDF, hfFC, hcFC, ?_, ?_, ?_⟩ <;> euclid_finish

end Elements.Book1
