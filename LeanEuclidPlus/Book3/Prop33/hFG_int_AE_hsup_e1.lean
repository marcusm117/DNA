import SystemE
import Book1.Prop13.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

-- Angles on a straight line (Euclid I.13): e0, a, e1 collinear with a between, so
-- ∠e0:a:b + ∠e1:a:b = 2∟.  (AB ≠ AE holds since e0 ∈ AE but e0 ∉ AB.)
theorem helper_3_33_hFG_int_AE_hsup_e1
    (a b e0 e1 : Point) (AE AB : Line)
    (haae : a.onLine AE) (he0ae : e0.onLine AE) (he1ae : e1.onLine AE)
    (hab : a.onLine AB) (hbb : b.onLine AB) (hne : a ≠ b) (he0offAB : ¬ e0.onLine AB)
    (he1 : between e0 a e1) :
    ∠ e0:a:b + ∠ e1:a:b = ∟ + ∟ := by
  euclid_apply (proposition_13 b a e1 e0 AB AE)
  euclid_finish

end Elements.Book3
