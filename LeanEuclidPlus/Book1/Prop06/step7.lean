import SystemE
import Book1.Prop04.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

/- 1.6.7: the base DC equals the base AB. SAS (proposition_4) on triangles DBC and ACB: |b─d|=|a─c|
   (construction), |b─c|=|c─b| (segment symmetry), included angle ∠d:b:c = ∠a:c:b (step6) ⟹
   |d─c| = |a─b|. The full SAS conclusion is obtained then the base conjunct extracted. -/
theorem helper_1_6_step7 (a b c d : Point) (AB BC AC DC : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hABneBC : AB ≠ BC) (hBCneAC : BC ≠ AC) (hACneAB : AC ≠ AB)
    (hbda : between b d a) (hdDC : d.onLine DC) (hcDC : c.onLine DC)
    (hbdac : |(b─d)| = |(a─c)|) (hdbc_acb : ∠ d:b:c = ∠ a:c:b) :
    |(d─c)| = |(a─b)| := by
  have hfull : |(d─c)| = |(a─b)| ∧ (∠ b:d:c = ∠ c:a:b) ∧ (∠ b:c:d = ∠ c:b:a) := by
    euclid_apply (proposition_4 b d c c a b AB DC BC AC AB BC)
    (try split_ands) <;> assumption
  exact hfull.1

end Elements.Book1
