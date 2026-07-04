import SystemE
import Book.Prop13
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_15_step1
  (a b c d e : Point) (AB CD : Line)
  (ha : a.onLine AB) (hb : b.onLine AB) (he_AB : e.onLine AB)
  (hc : c.onLine CD) (hd : d.onLine CD) (hcd : c ≠ d)
  (he_CD : e.onLine CD)
  (hne : CD ≠ AB)
  (h_aeb : between a e b)
  (hassump1 : between d e c)
  : ∠ c:e:a + ∠ a:e:d = ∟ + ∟ := by
  euclid_apply (proposition_13 a e c d AB CD)
  euclid_finish

end Elements.Book1
