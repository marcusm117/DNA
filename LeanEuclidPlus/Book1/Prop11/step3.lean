import SystemE
import Book1.Prop11.step3_foff
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_11_step3
    (a b c d e f : Point) (AB DF FE : Line)
    (hacb : between a c b)
    (ha : a.onLine AB) (hb : b.onLine AB) (hab : a ≠ b)
    (hdAB : d.onLine AB) (hdc : between c d a) (hce : between c e b)
    (hfd : |(f─d)| = |(d─e)|) (hfe : |(f─e)| = |(d─e)|)
    (hdDF : d.onLine DF) (hfDF : f.onLine DF)
    (hfFE : f.onLine FE) (heFE : e.onLine FE) :
    formTriangle f d e DF AB FE ∧ |(f─d)| = |(d─e)| ∧ |(f─e)| = |(d─e)| := by
  have step3_foff : ¬(f.onLine AB) := by euclid_apply (helper_1_11_step3_foff a b c d e f AB (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between c d a; assumption)) (by euclid_assumption "" (show between c e b; assumption)) (by euclid_assumption "" (show |(f─d)| = |(d─e)|; assumption)) (by euclid_assumption "" (show |(f─e)| = |(d─e)|; assumption)))
  refine ⟨?_, hfd, hfe⟩
  refine ⟨⟨hfDF, hdDF, ?_⟩, hdAB, ?_, heFE, hfFE, ?_, ?_, ?_⟩ <;> euclid_finish

end Elements.Book1
