import SystemE
import Book.Prop13
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_15_step2
  (a b d e : Point) (AB CD : Line)
  (ha : a.onLine AB) (hb : b.onLine AB) (hab : a ≠ b)
  (hd : d.onLine CD) (he_CD : e.onLine CD)
  (he_AB : e.onLine AB)
  (hne : CD ≠ AB)
  (h_dec : between d e c)
  (hassump1 : between a e b)
  : ∠ a:e:d + ∠ d:e:b = ∟ + ∟ := by
  euclid_apply (proposition_13 d e a b CD AB)
  euclid_finish

end Elements.Book1
