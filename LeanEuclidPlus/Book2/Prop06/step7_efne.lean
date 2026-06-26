import SystemE
import Book2.Prop06.step2_eoff
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7 sub: EF ≠ AB. e ∈ EF but e ∉ AB — e ∉ AB reuses step2_eoff (the right-angle degeneracy). -/
theorem helper_2_6_step7_efne (a b c d e : Point) (AB CE EF : Line)
    (heEF : e.onLine EF)
    (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hacb : between a c b) (habd : between a b d)
    (hce : |(c─e)| = |(c─d)|) (hdce : ∠ d:c:e = ∟) :
    EF ≠ AB := by
  have step2_eoff : ¬(e.onLine AB) := by euclid_apply (helper_2_6_step2_eoff a b c d e AB (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─d)|; assumption)) (by euclid_assumption "" (show ∠ d:c:e = ∟; assumption)))
  exact fun heq => step2_eoff (heq ▸ heEF)

end Elements.Book2
