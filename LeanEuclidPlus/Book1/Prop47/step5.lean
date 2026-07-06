import SystemE
import Book1.Prop14.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step5
    (a b c g : Point) (AB AC AG : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC)
    (ha_AG : a.onLine AG) (hg_AG : g.onLine AG)
    (h_g_nsame : ¬g.sameSide c AB) (h_g_nAB : ¬g.onLine AB) (h_c_nAB : ¬c.onLine AB)
    (h_bac : (∠ b:a:c : ℝ) = ∟) (h_bag : (∠ b:a:g : ℝ) = ∟) :
    between c a g := by
  euclid_apply (proposition_14 b a c g AB AC AG)
  euclid_finish

end Elements.Book1
