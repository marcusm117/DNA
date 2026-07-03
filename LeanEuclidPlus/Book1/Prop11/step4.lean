import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_11_step4
    (a b c d e f : Point) (AB FC : Line)
    (hacb : between a c b) (ha : a.onLine AB) (hb : b.onLine AB)
    (hdAB : d.onLine AB) (hdc : between c d a) (hce : between c e b)
    (hcd_lt : |(c─d)| < |(c─b)|) (hce_eq : |(c─e)| = |(c─d)|)
    (hfd : |(f─d)| = |(d─e)|) (hfe : |(f─e)| = |(d─e)|)
    (hfFC : f.onLine FC) (hcFC : c.onLine FC) :
    distinctPointsOnLine f c FC := by
  refine ⟨hfFC, hcFC, ?_⟩
  euclid_finish

end Elements.Book1
