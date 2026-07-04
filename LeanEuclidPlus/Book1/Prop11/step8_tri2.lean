import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_11_step8_tri2
    (a b c d e f : Point) (AB FE FC : Line)
    (hacb : between a c b) (ha : a.onLine AB) (hb : b.onLine AB) (hab : a ≠ b)
    (hdAB : d.onLine AB) (hdc : between c d a) (hce : between c e b)
    (hfd : |(f─d)| = |(d─e)|) (hfe : |(f─e)| = |(d─e)|)
    (hfFE : f.onLine FE) (heFE : e.onLine FE)
    (hfFC : f.onLine FC) (hcFC : c.onLine FC)
    (hABneFE : AB ≠ FE) :
    formTriangle c e f AB FE FC := by
  refine ⟨⟨?_, ?_, ?_⟩, heFE, hfFE, hfFC, hcFC, ?_, ?_, ?_⟩ <;> euclid_finish

end Elements.Book1
