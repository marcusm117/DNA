import SystemE
import Book1.Prop04.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

/- 1.6.8: the triangle DBC is equal to the triangle ACB [Prop.~1.4] — the full SAS congruence
   conclusion: base |d─c| = |a─b| plus the two remaining angles ∠b:d:c = ∠c:a:b and
   ∠b:c:d = ∠c:b:a. Same SAS application as step7 (sides + included angle), full conclusion. -/
theorem helper_1_6_step8 (a b c d : Point) (AB BC AC DC : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hABneBC : AB ≠ BC) (hBCneAC : BC ≠ AC) (hACneAB : AC ≠ AB)
    (hbda : between b d a) (hdDC : d.onLine DC) (hcDC : c.onLine DC)
    (hbdac : |(b─d)| = |(a─c)|) (hdbc_acb : ∠ d:b:c = ∠ a:c:b) :
    |(d─c)| = |(a─b)| ∧ (∠ b:d:c = ∠ c:a:b) ∧ (∠ b:c:d = ∠ c:b:a) := by
  euclid_apply (proposition_4 b d c c a b AB DC BC AC AB BC)
  (try split_ands) <;> assumption

end Elements.Book1
