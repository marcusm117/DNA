import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_13_step1 (a b c d : Point) (AB CD : Line)
    (hAB_ne_CD : AB ≠ CD) (ha : a.onLine AB) (hb : b.onLine AB) (hab : a ≠ b)
    (hbetween : between d b c) (hc : c.onLine CD) (hd : d.onLine CD) (hcd : c ≠ d)
    (h_eq : ∠ c:b:a = ∠ a:b:d) :
    ∠ c:b:a = ∟ ∧ ∠ a:b:d = ∟ := by
  euclid_finish

end Elements.Book1
