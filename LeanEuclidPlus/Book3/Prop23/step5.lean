import SystemE
import Book1.Prop16.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_23_step5 (a b c d : Point) (AB ACD CB DB : Line)
    (h_aAB : a.onLine AB) (h_bAB : b.onLine AB) (h_ab : a ≠ b)
    (h_aACD : a.onLine ACD) (h_cACD : c.onLine ACD) (h_dACD : d.onLine ACD)
    (h_cCB : c.onLine CB) (h_bCB : b.onLine CB)
    (h_dDB : d.onLine DB) (h_bDB : b.onLine DB)
    (h_cd : c.sameSide d AB) (h_bet : between a c d)
    (h_ang : ∠ a:c:b = ∠ a:d:b) : False := by
  euclid_apply (Elements.Book1.proposition_16 b d c a DB ACD CB)
  euclid_finish

end Elements.Book3
