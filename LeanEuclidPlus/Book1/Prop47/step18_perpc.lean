import SystemE
import Book.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- Ported helper_47_AL_perp_BC on the CE side: AL ∥ CE, CE ⊥ BC (∠b:c:e=∟) ⟹ ∠a:m:c = ∟.
theorem helper_1_47_step18_perpc
    (a b c e m : Point) (BC CE AL : Line)
    (ha_AL : a.onLine AL) (hm_AL : m.onLine AL) (ham : a ≠ m)
    (hc_BC : c.onLine BC) (hb_BC : b.onLine BC) (hm_BC : m.onLine BC) (hcb : c ≠ b) (hcm : c ≠ m)
    (hc_CE : c.onLine CE) (he_CE : e.onLine CE) (hce : c ≠ e)
    (h_a_nBC : ¬a.onLine BC) (h_e_nBC : ¬e.onLine BC) (h_a_nCE : ¬a.onLine CE)
    (hBCCE : BC ≠ CE) (hALCE : AL ≠ CE)
    (h_bce : (∠ b:c:e : ℝ) = ∟)
    (h_nALCE : ¬AL.intersectsLine CE)
    (h_ne_same_a_BC : ¬e.sameSide a BC) :
    (∠ a:m:c : ℝ) = ∟ := by
  euclid_apply (proposition_29''' a e m c AL CE BC)
  euclid_finish

end Elements.Book1
