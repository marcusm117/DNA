import SystemE
import Book1Variants.Prop05
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_19_step3 (a b c : Point) (AB BC AC : Line)
    (h_aAB : a.onLine AB) (h_bAB : b.onLine AB) (h_bBC : b.onLine BC) (h_cBC : c.onLine BC)
    (h_cAC : c.onLine AC) (h_aAC : a.onLine AC)
    (h_ABneBC : AB ≠ BC) (h_BCneAC : BC ≠ AC) (h_ACneAB : AC ≠ AB)
    (h_aneb : a ≠ b)
    (h_eq : |(a─c)| = |(a─b)|) :
    ∠ a:b:c = ∠ b:c:a := by
  euclid_apply (proposition_5' a b c AB BC AC)
  euclid_finish

end Elements.Book1
