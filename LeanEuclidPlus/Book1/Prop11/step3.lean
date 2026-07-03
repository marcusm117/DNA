import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_11_step3
    (a b c d e f : Point) (AB DF FE : Line)
    (hacb : between a c b)
    (ha : a.onLine AB) (hb : b.onLine AB) (hab : a ≠ b)
    (hdAB : d.onLine AB) (hdc : between c d a) (hce : between c e b)
    (hfd : |(f─d)| = |(d─e)|) (hfe : |(f─e)| = |(d─e)|)
    (hdDF : d.onLine DF) (hfDF : f.onLine DF)
    (hfFE : f.onLine FE) (heFE : e.onLine FE) :
    formTriangle f d e DF AB FE ∧ |(f─d)| = |(d─e)| ∧ |(f─e)| = |(d─e)| := by
  have step3_foff : ¬(f.onLine AB) := by sorry
  refine ⟨?_, hfd, hfe⟩
  refine ⟨⟨hfDF, hdDF, ?_⟩, hdAB, ?_, heFE, hfFE, ?_, ?_, ?_⟩ <;> euclid_finish

end Elements.Book1
