import SystemE
import Book1.Prop29.variants
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- Ported helper_47_AL_perp_BC (l'=m): AL ∥ BD, BD ⊥ BC (∠c:b:d=∟) ⟹ AL ⊥ BC, i.e. ∠a:m:b = ∟.
theorem helper_1_47_step18_perp
    (a b c d m : Point) (BC BD AL : Line)
    (ha_AL : a.onLine AL) (hm_AL : m.onLine AL) (ham : a ≠ m)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC) (hm_BC : m.onLine BC) (hbc : b ≠ c) (hbm : b ≠ m)
    (hb_BD : b.onLine BD) (hd_BD : d.onLine BD) (hbd : b ≠ d)
    (h_a_nBC : ¬a.onLine BC) (h_d_nBC : ¬d.onLine BC) (h_a_nBD : ¬a.onLine BD)
    (hBCBD : BC ≠ BD) (hALBD : AL ≠ BD)
    (h_cbd : (∠ c:b:d : ℝ) = ∟)
    (h_nALBD : ¬AL.intersectsLine BD)
    (h_nd_same_a_BC : ¬d.sameSide a BC) :
    (∠ a:m:b : ℝ) = ∟ := by
  euclid_apply (proposition_29''' a d m b AL BD BC)
  euclid_finish

end Elements.Book1
