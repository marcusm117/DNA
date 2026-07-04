import SystemE
import Book.Prop13
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_15_step7
  (a b c d e : Point) (AB CD : Line)
  (ha : a.onLine AB) (hb : b.onLine AB) (hab : a ≠ b)
  (hc : c.onLine CD) (hd : d.onLine CD) (hcd : c ≠ d)
  (he_AB : e.onLine AB) (he_CD : e.onLine CD)
  (hne : CD ≠ AB)
  (h_dec : between d e c)
  (h_aeb : between a e b)
  (hstep2 : ∠ a:e:d + ∠ d:e:b = ∟ + ∟)
  : ∠ c:e:b = ∠ d:e:a := by
  euclid_apply (proposition_13 b e c d AB CD)
  euclid_finish

end Elements.Book1
