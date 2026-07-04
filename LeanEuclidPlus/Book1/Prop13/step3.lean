import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_13_step3 (a b c d e : Point) (AB CD BE : Line)
    (hAB_ne_CD : AB ≠ CD) (ha : a.onLine AB) (hb : b.onLine AB) (hab : a ≠ b)
    (hbetween : between d b c) (hc : c.onLine CD) (hd : d.onLine CD) (hcd : c ≠ d)
    (h_sameside : e.sameSide a CD) (hcbe : ∠ c:b:e = ∟)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (step2 : distinctPointsOnLine b e BE ∧ ∠ c:b:e = ∟) :
    ∠ c:b:e = ∟ ∧ ∠ e:b:d = ∟ := by
  euclid_finish

end Elements.Book1
