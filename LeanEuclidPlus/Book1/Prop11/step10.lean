import SystemE
import Book1.Prop11.step10_foff
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_11_step10
    (a b c d e f : Point) (AB : Line)
    (hacb : between a c b) (ha : a.onLine AB) (hb : b.onLine AB) (hab : a ≠ b)
    (hdAB : d.onLine AB) (hdc : between c d a) (hce : between c e b)
    (hfd : |(f─d)| = |(d─e)|) (hfe : |(f─e)| = |(d─e)|)
    -- Reasoning hypotheses (from @assumption — keep these types in the signature):
    (hassump1 : ∠ d:c:f = ∠ e:c:f ∧ between d c e)   -- "a straight-line stood on  a(nother) straight-line makes the adjacent angles equal to one another"
    : ∠ d:c:f = ∟ ∧ ∠ f:c:e = ∟ := by
  have step10_foff : ¬(f.onLine AB) := by euclid_apply (helper_1_11_step10_foff a b c d e f AB (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between c d a; assumption)) (by euclid_assumption "" (show between c e b; assumption)) (by euclid_assumption "" (show |(f─d)| = |(d─e)|; assumption)) (by euclid_assumption "" (show |(f─e)| = |(d─e)|; assumption)))
  obtain ⟨hangle_eq, hbetween⟩ := hassump1
  constructor
  · euclid_apply (perpendicular_if d e c f AB)
    euclid_finish
  · euclid_finish

end Elements.Book1
