import SystemE
import Book.Prop14
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step6
    (a b c h : Point) (AB AC AH : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC) (h_c_nAB : ¬c.onLine AB)
    (ha_AH : a.onLine AH) (hh_AH : h.onLine AH)
    (h_h_nsame : ¬h.sameSide b AC) (h_h_nAC : ¬h.onLine AC) (h_b_nAC : ¬b.onLine AC)
    (h_bac : (∠ b:a:c : ℝ) = ∟) (h_cah : (∠ c:a:h : ℝ) = ∟) :
    between b a h := by
  euclid_apply (proposition_14 c a b h AC AB AH)
  euclid_finish

end Elements.Book1
