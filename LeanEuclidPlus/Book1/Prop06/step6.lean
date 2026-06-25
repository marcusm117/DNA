import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

/- 1.6.6: the angle DBC equals the angle ACB. `between b d a` puts d on the ray b→a, so on line AB
   (with a,b) `equal_angles b d a c c AB BC` yields ∠d:b:c = ∠a:b:c; with the hypothesis
   ∠a:b:c = ∠a:c:b, ∠d:b:c = ∠a:c:b. The full formTriangle atom set is passed so the `equal_angles`
   precondition (d.onLine AB, c≠b, ¬between d b a) discharges. -/
theorem helper_1_6_step6 (a b c d : Point) (AB BC AC : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hABneBC : AB ≠ BC) (hBCneAC : BC ≠ AC) (hACneAB : AC ≠ AB)
    (hbda : between b d a) (habc_acb : ∠ a:b:c = ∠ a:c:b) :
    ∠ d:b:c = ∠ a:c:b := by
  have hdb_abc : ∠ d:b:c = ∠ a:b:c := by
    euclid_apply (equal_angles b d a c c AB BC)
    assumption
  exact hdb_abc.trans habc_acb

end Elements.Book1
