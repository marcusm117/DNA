import SystemE
import Book.Prop30
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- AL ∥ BD and CE ∥ BD ⟹ AL ∥ CE (parallel transitivity, proposition_30). Main never establishes this.
theorem helper_1_47_step17_ALCE
    (a b c : Point) (AL CE BD BC : Line)
    (ha_AL : a.onLine AL) (hoffBD : ¬a.onLine BD) (h_offCE : ¬a.onLine CE)
    (hb_BD : b.onLine BD) (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hc_CE : c.onLine CE) (h_c_nBD : ¬c.onLine BD)
    (h_nALBD : ¬AL.intersectsLine BD) (h_nBDCE : ¬BD.intersectsLine CE) :
    ¬AL.intersectsLine CE := by
  euclid_apply (proposition_30 AL CE BD)
  euclid_finish

end Elements.Book1
